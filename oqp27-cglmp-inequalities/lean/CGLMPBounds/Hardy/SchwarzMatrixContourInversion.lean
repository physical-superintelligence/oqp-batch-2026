module

public import CGLMPBounds.Hardy.SchwarzFinitePoleTransport
public import CGLMPBounds.Hardy.SchwarzRationalTrace
public import CGLMPBounds.Hardy.SchwarzInversionSpectrum

@[expose] public section


/-! Actual C.7 contour inversion for the matrix integrand. Partial fractions
are constructed from its characteristic polynomial and adjugate numerator,
then transported summand by summand with actual circle integrability. The
source q contour is first deformed away from zero. No matrix contour
identity, rational expansion or spectral selector is assumed by the final
q coefficient formula. -/

open Complex Metric Set Polynomial
open scoped Matrix.Norms.Operator

namespace CGLMPBounds.Hardy
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

lemma matrix_root_ne_zero {H : Matrix ι ι ℂ} (hdet : IsUnit H.det)
    {a : ℂ} (ha : a ∈ H.charpoly.roots) : a ≠ 0 := by
  intro he
  exact (spectrum.zero_notMem ℂ ((Matrix.isUnit_iff_isUnit_det H).mpr hdet))
    (he ▸ Matrix.mem_spectrum_of_isRoot_charpoly (Polynomial.isRoot_of_mem_roots ha))

/-- Genuine inversion transport for the actual weighted matrix trace. The
hypotheses are exclusively explicit circle geometry and invertibility. -/
theorem circleIntegral_inverse_pullback_weighted_resolvent
    (H Y : Matrix ι ι ℂ) (hdet : IsUnit H.det) (m n : ℕ)
    {c d : ℂ} {R S : ℝ} (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hzero : (0 : ℂ) ∉ closedBall c R)
    (hsrc : ∀ a ∈ H.charpoly.roots, a⁻¹ ∉ sphere c R)
    (htgt : ∀ a ∈ H.charpoly.roots, a ∉ sphere d S)
    (hselect : ∀ a ∈ H.charpoly.roots, a⁻¹ ∈ ball c R ↔ a ∈ ball d S) :
    (∮ z in C(c, R), -(z ^ 2)⁻¹ *
      ((z⁻¹) ^ m * Matrix.trace ((resolvent H z⁻¹ * Y) ^ n))) =
      ∮ z in C(d, S), z ^ m * Matrix.trace ((resolvent H z * Y) ^ n) := by
  classical
  obtain ⟨q, b, he⟩ := weighted_resolvent_trace_has_partial_fractions H Y m n
  let s := H.charpoly.roots.toFinset
  let κ := Σ a : s, Fin (H.charpoly.roots.count a.val * n)
  let poles : κ → ℂ := fun i => i.1.val
  let coeff : κ → ℂ := fun i => b i.1.val i.2
  let powers : κ → ℕ := fun i => i.2.val + 1
  let F : ℂ → ℂ := fun z => q.eval z + ∑ i : κ, coeff i * (z - poles i)⁻¹ ^ powers i
  have hroots (i : κ) : poles i ∈ H.charpoly.roots := Multiset.mem_toFinset.mp i.1.property
  have hdecomp : ∀ z : ℂ, z ∉ spectrum ℂ H →
      z ^ m * Matrix.trace ((resolvent H z * Y) ^ n) = F z := by
    intro z hz
    rw [he z hz]
    simp only [F, coeff, poles, powers, κ, Fintype.sum_sigma]
    exact congrArg (fun v : ℂ => q.eval z + v)
      (Finset.sum_coe_sort s (fun a : ℂ =>
        ∑ j : Fin (H.charpoly.roots.count a * n),
          b a j * (z - a)⁻¹ ^ (j.val + 1))).symm
  have hsrcoff : ∀ z ∈ sphere c R, z⁻¹ ∉ spectrum ℂ H := by
    intro z hz hs
    have hr : z⁻¹ ∈ H.charpoly.roots :=
      (Polynomial.mem_roots H.charpoly_monic.ne_zero).mpr
        (Matrix.mem_spectrum_iff_isRoot_charpoly.mp hs)
    exact hsrc z⁻¹ hr (by simpa only [inv_inv] using hz)
  calc
    _ = ∮ z in C(c, R), -(z ^ 2)⁻¹ * F z⁻¹ := by
      apply circleIntegral.integral_congr hR
      intro z hz
      dsimp only
      rw [hdecomp z⁻¹ (hsrcoff z hz)]
    _ = ∮ z in C(d, S), F z := by
      exact circleIntegral_inverse_pullback_finite_poles Finset.univ q poles coeff powers
        hR hS hzero (fun i _ => matrix_root_ne_zero hdet (hroots i))
        (fun i _ => hsrc _ (hroots i)) (fun i _ => htgt _ (hroots i))
        (fun i _ => hselect _ (hroots i))
    _ = _ := by
      apply circleIntegral.integral_congr hS
      intro z hz
      exact (hdecomp z (circle_not_mem_spectrum_of_root_separation H htgt hz)).symm

lemma inverse_pencil_trace_eq_signed_pullback (H Y : Matrix ι ι ℂ)
    {ζ : ℂ} (hζ : ζ ≠ 0) {n : ℕ} (hn : 2 ≤ n) :
    (-1 : ℂ) ^ n * Matrix.trace ((Ring.inverse (ζ • H - 1) * Y) ^ n) =
      (-1 : ℂ) * (-(ζ ^ 2)⁻¹ *
        ((ζ⁻¹) ^ (n - 2) * Matrix.trace ((resolvent H ζ⁻¹ * Y) ^ n))) := by
  rw [inverse_pencil_power_trace H Y hζ]
  have hsign : (-1 : ℂ) ^ n * (-ζ⁻¹) ^ n = (ζ⁻¹) ^ n := by
    rw [← mul_pow]
    congr 1
    ring
  have hpower : (ζ ^ 2)⁻¹ * (ζ⁻¹) ^ (n - 2) = (ζ⁻¹) ^ n := by
    rw [← inv_pow, ← pow_add]
    congr 1
    omega
  calc
    _ = (ζ⁻¹) ^ n * Matrix.trace ((resolvent H ζ⁻¹ * Y) ^ n) := by
      rw [← mul_assoc, hsign]
    _ = _ := by rw [← hpower]; ring

/-- The second actual contour line of C.7. This states q_n on the inverted
negative H circle with the correct differential minus sign. The separate
negative/positive contour comparison is still required for full C.7. -/
theorem exteriorTaylorCoefficient_eq_inverted_negative_contour
    {H : Matrix ι ι ℂ} (Y : Matrix ι ι ℂ) (hH : H.IsHermitian)
    (hdet : IsUnit H.det) {n : ℕ} (hn : 2 ≤ n) :
    let R := negativeClusterRadius H⁻¹.charpoly.roots
    ∃ r : ℝ, 0 < r ∧ r < R ∧
      (∀ a ∈ H.charpoly.roots,
        a ∉ sphere (((-R / (R ^ 2 - r ^ 2)) : ℝ) : ℂ) (r / (R ^ 2 - r ^ 2)) ∧
        (a ∈ ball (((-R / (R ^ 2 - r ^ 2)) : ℝ) : ℂ) (r / (R ^ 2 - r ^ 2)) ↔
          a.re < 0)) ∧
      exteriorTaylorCoefficient H Y n = -(1 / (n : ℂ)) *
        (∮ z in C((((-R / (R ^ 2 - r ^ 2)) : ℝ) : ℂ), (r / (R ^ 2 - r ^ 2))),
          z ^ (n - 2) * Matrix.trace ((resolvent H z * Y) ^ n)) /
            (2 * Real.pi * Complex.I : ℂ) / (Fintype.card ι : ℂ) := by
  let R := negativeClusterRadius H⁻¹.charpoly.roots
  obtain ⟨r, hr0, hrR, hzero, hselect, hq⟩ :=
    exteriorTaylorCoefficient_eq_safe_negative_resolvent_power Y hH hdet (by omega : 0 < n)
  let c : ℂ := (((-R / (R ^ 2 - r ^ 2)) : ℝ) : ℂ)
  let S : ℝ := r / (R ^ 2 - r ^ 2)
  have hΔ : 0 < (-R) ^ 2 - r ^ 2 := by
    have hR0 : 0 < R := negativeClusterRadius_pos _
    nlinarith
  have hS : 0 ≤ S := div_nonneg hr0.le (by simpa only [neg_sq] using hΔ.le)
  have hsrc : ∀ a ∈ H.charpoly.roots, a⁻¹ ∉ sphere (-(R : ℂ)) r := by
    intro a ha
    exact (hselect a⁻¹ ((inverse_mem_matrix_roots_iff hdet a).mpr ha)).1
  have himage : ∀ a ∈ H.charpoly.roots,
      (a⁻¹ ∈ sphere (-(R : ℂ)) r ↔ a ∈ sphere c S) ∧
      (a⁻¹ ∈ ball (-(R : ℂ)) r ↔ a ∈ ball c S) := by
    intro a ha
    exact ⟨by simpa only [neg_sq, Complex.ofReal_neg] using
      inverse_mem_real_sphere_iff hr0.le hΔ (matrix_root_ne_zero hdet ha),
      by simpa only [neg_sq, Complex.ofReal_neg] using
      inverse_mem_real_ball_iff hr0.le hΔ (matrix_root_ne_zero hdet ha)⟩
  have htgt : ∀ a ∈ H.charpoly.roots, a ∉ sphere c S :=
    fun a ha hs => hsrc a ha ((himage a ha).1.mpr hs)
  refine ⟨r, hr0, hrR, ?_, ?_⟩
  · intro a ha
    refine ⟨htgt a ha, (himage a ha).2.symm.trans ?_⟩
    exact ((hselect a⁻¹ ((inverse_mem_matrix_roots_iff hdet a).mpr ha)).2).trans
      (inverse_re_neg_iff (matrix_root_ne_zero hdet ha))
  · have htransport := circleIntegral_inverse_pullback_weighted_resolvent H Y hdet
      (n - 2) n hr0.le hS hzero hsrc htgt (fun a ha => (himage a ha).2)
    have hsign : (-1 : ℂ) ^ n *
        (∮ ζ in C((-(R : ℂ)), r), Matrix.trace ((Ring.inverse (ζ • H - 1) * Y) ^ n)) =
        (-1 : ℂ) * (∮ z in C(c, S),
          z ^ (n - 2) * Matrix.trace ((resolvent H z * Y) ^ n)) := by
      rw [← circleIntegral.integral_const_mul, ← htransport,
        ← circleIntegral.integral_const_mul]
      apply circleIntegral.integral_congr hr0.le
      intro ζ hζ
      exact inverse_pencil_trace_eq_signed_pullback H Y
        (fun he => hzero (he ▸ sphere_subset_closedBall hζ)) hn
    rw [hq, div_mul_eq_mul_div, hsign]
    ring

end
end CGLMPBounds.Hardy
