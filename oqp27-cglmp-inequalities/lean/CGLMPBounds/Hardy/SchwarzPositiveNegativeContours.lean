module

public import CGLMPBounds.Hardy.SchwarzFinitePoleIntegral
public import CGLMPBounds.Hardy.SchwarzResolventOuterDecay
public import CGLMPBounds.Hardy.SchwarzMatrixContourInversion
public import CGLMPBounds.Hardy.SchwarzPositiveCoefficients

@[expose] public section


/-! The actual negative/positive C.7 contour comparison. Finite partial
fractions prove that complementary pole circles add to a sufficiently large
outer circle. The actual inverse-square decay then makes this common value
zero. This does not assume a total-residue cancellation or contour equality. -/

open Complex Metric Set Filter Polynomial
open scoped Topology Matrix.Norms.Operator

namespace CGLMPBounds.Hardy
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

/-- Any two actual pole-separating circles whose disks partition the roots
have opposite C.7 weighted trace integrals. -/
theorem weighted_resolvent_circle_partition_sum_zero (H Y : Matrix ι ι ℂ)
    {n : ℕ} (hn : 2 ≤ n) {c₁ c₂ : ℂ} {R₁ R₂ : ℝ}
    (hR₁ : 0 ≤ R₁) (hR₂ : 0 ≤ R₂)
    (hsep₁ : ∀ a ∈ H.charpoly.roots, a ∉ sphere c₁ R₁)
    (hsep₂ : ∀ a ∈ H.charpoly.roots, a ∉ sphere c₂ R₂)
    (hpartition : ∀ a ∈ H.charpoly.roots, a ∈ ball c₁ R₁ ↔ a ∉ ball c₂ R₂) :
    (∮ z in C(c₁, R₁), z ^ (n - 2) * Matrix.trace ((resolvent H z * Y) ^ n)) +
      (∮ z in C(c₂, R₂), z ^ (n - 2) * Matrix.trace ((resolvent H z * Y) ^ n)) = 0 := by
  classical
  obtain ⟨q, b, he⟩ := weighted_resolvent_trace_has_partial_fractions H Y (n - 2) n
  let s := H.charpoly.roots.toFinset
  let κ := Σ a : s, Fin (H.charpoly.roots.count a.val * n)
  let poles : κ → ℂ := fun i => i.1.val
  let coeff : κ → ℂ := fun i => b i.1.val i.2
  let powers : κ → ℕ := fun i => i.2.val + 1
  let F : ℂ → ℂ := fun z => q.eval z + ∑ i : κ, coeff i * (z - poles i)⁻¹ ^ powers i
  let G : ℂ → ℂ := fun z => z ^ (n - 2) * Matrix.trace ((resolvent H z * Y) ^ n)
  have hroots (i : κ) : poles i ∈ H.charpoly.roots := Multiset.mem_toFinset.mp i.1.property
  have hdecomp : ∀ z : ℂ, z ∉ spectrum ℂ H → G z = F z := by
    intro z hz
    dsimp only [G]
    rw [he z hz]
    simp only [F, coeff, poles, powers, κ, Fintype.sum_sigma]
    exact congrArg (fun v : ℂ => q.eval z + v)
      (Finset.sum_coe_sort s (fun a : ℂ =>
        ∑ j : Fin (H.charpoly.roots.count a * n),
          b a j * (z - a)⁻¹ ^ (j.val + 1))).symm
  have hI {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
      (hsep : ∀ a ∈ H.charpoly.roots, a ∉ sphere c R) :
      (∮ z in C(c, R), G z) = ∮ z in C(c, R), F z := by
    apply circleIntegral.integral_congr hR
    intro z hz
    exact hdecomp z (circle_not_mem_spectrum_of_root_separation H hsep hz)
  let M : ℝ := 1 + ∑ a ∈ s, ‖a‖
  have hM : 0 < M := by dsimp [M]; positivity
  have hevent : ∀ᶠ R : ℝ in atTop,
      (∮ z in C(c₁, R₁), G z) + (∮ z in C(c₂, R₂), G z) =
        ∮ z in C(0, R), G z := by
    filter_upwards [eventually_gt_atTop M] with R hR
    have hRp : 0 < R := hM.trans hR
    have houter : ∀ a ∈ H.charpoly.roots, a ∈ ball (0 : ℂ) R := by
      intro a ha
      have hle : ‖a‖ ≤ ∑ b ∈ s, ‖b‖ :=
        Finset.single_le_sum (fun b _ => norm_nonneg b) (Multiset.mem_toFinset.mpr ha)
      have hlt : ‖a‖ < R := by dsimp [M] at hR; linarith
      simpa only [Metric.mem_ball, dist_zero_right] using hlt
    have hsep₃ : ∀ a ∈ H.charpoly.roots, a ∉ sphere (0 : ℂ) R := by
      intro a ha hs
      have hlt : dist a 0 < R := houter a ha
      have heq := Metric.mem_sphere.mp hs
      linarith
    rw [hI hR₁ hsep₁, hI hR₂ hsep₂, hI hRp.le hsep₃]
    exact circleIntegral_finite_poles_partition Finset.univ q poles coeff powers
      hR₁ hR₂ hRp.le (fun i _ => hsep₁ _ (hroots i))
      (fun i _ => hsep₂ _ (hroots i)) (fun i _ => hsep₃ _ (hroots i))
      (fun i _ => houter _ (hroots i)) (fun i _ => hpartition _ (hroots i))
  have ht : Tendsto (fun _ : ℝ =>
      (∮ z in C(c₁, R₁), G z) + (∮ z in C(c₂, R₂), G z)) atTop (𝓝 0) :=
    (tendsto_weighted_resolvent_outerCircle_zero H Y hn).congr'
      (hevent.mono (fun _ h => h.symm))
  exact tendsto_nhds_unique tendsto_const_nhds ht

/-- The actual positive-contour formula for the exterior q coefficient,
with the negative/positive comparison proved by decay, not postulated. -/
theorem exteriorTaylorCoefficient_eq_positive_resolvent_power
    {H : Matrix ι ι ℂ} (Y : Matrix ι ι ℂ) (hH : H.IsHermitian)
    (hdet : IsUnit H.det) {n : ℕ} (hn : 2 ≤ n) :
    let P := negativeClusterRadius H.charpoly.roots
    exteriorTaylorCoefficient H Y n = (1 / (n : ℂ)) *
      (∮ z in C((P : ℂ), P), z ^ (n - 2) * Matrix.trace ((resolvent H z * Y) ^ n)) /
        (2 * Real.pi * Complex.I : ℂ) / (Fintype.card ι : ℂ) := by
  let R := negativeClusterRadius H⁻¹.charpoly.roots
  let P := negativeClusterRadius H.charpoly.roots
  obtain ⟨r, hr0, hrR, hneg, hq⟩ :=
    exteriorTaylorCoefficient_eq_inverted_negative_contour Y hH hdet hn
  have hΔ : 0 < R ^ 2 - r ^ 2 := by
    have hR0 : 0 < R := negativeClusterRadius_pos _
    nlinarith
  have hS : 0 ≤ r / (R ^ 2 - r ^ 2) := div_nonneg hr0.le hΔ.le
  have hpos := fun a ha => positiveClusterRadius_separates H.charpoly.roots
    (fun b hb => hermitian_root_re_ne_zero hH hdet hb) (a := a) ha
  have hpartition : ∀ a ∈ H.charpoly.roots,
      a ∈ ball (((-R / (R ^ 2 - r ^ 2)) : ℝ) : ℂ) (r / (R ^ 2 - r ^ 2)) ↔
        a ∉ ball (P : ℂ) P := by
    intro a ha
    rw [(hneg a ha).2, (hpos a ha).2]
    constructor
    · intro hneg hpos
      linarith
    · intro hnot
      exact lt_of_le_of_ne (le_of_not_gt hnot) (hermitian_root_re_ne_zero hH hdet ha)
  have hsum := weighted_resolvent_circle_partition_sum_zero H Y hn hS
    (negativeClusterRadius_pos _).le (fun a ha => (hneg a ha).1)
    (fun a ha => (hpos a ha).1) hpartition
  have heq := eq_neg_of_add_eq_zero_left hsum
  rw [hq, heq]
  ring

/-- The coefficient form of C.7: the actual positive-part real Taylor
coefficient equals (n−1) times the actual exterior q coefficient. -/
theorem positiveTraceTaylorCoefficient_eq_mul_exteriorTaylorCoefficient
    {H Y : Matrix ι ι ℂ} (hH : H.IsHermitian) (hY : Y.IsHermitian)
    (hdet : IsUnit H.det) {n : ℕ} (hn : 2 ≤ n) :
    (positiveTraceTaylorCoefficient H Y (n - 1) n : ℂ) =
      ((n - 1 : ℕ) : ℂ) * exteriorTaylorCoefficient H Y n := by
  rw [positiveTraceTaylorCoefficient_eq_positive_resolvent_power hH hY hdet hn,
    exteriorTaylorCoefficient_eq_positive_resolvent_power Y hH hdet hn]
  ring

end
end CGLMPBounds.Hardy
