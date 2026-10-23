module

public import CGLMPBounds.Hardy.CircleClusterTrace

@[expose] public section


/-!
# An explicit contour enclosing exactly the upper pencil roots

For a finite multiset without real roots, a sufficiently large circle centered
at `i*T`, of radius `T`, contains every upper root and excludes every lower
root even from its closed disk. The explicit radius below avoids any implicit
spectral-contour existence assumption. Multiplicities remain in the trace sum.

Applied to the Hermitian invertible pencil in Lemma C.3, this proves a literal
circle-integral representation of the source upper-cluster trace at each
upper-half-plane parameter. Holomorphy as the parameter varies, the real-axis
boundary value, and C.8 moments remain separate analytic obligations.
-/

open Complex Metric Set

namespace CGLMPBounds.Hardy
noncomputable section

def upperClusterRadius (s : Multiset ℂ) : ℝ :=
  1 + ∑ a ∈ s.toFinset, ‖a‖ ^ 2 / (2 * |a.im|)

lemma upperClusterRadius_pos (s : Multiset ℂ) : 0 < upperClusterRadius s := by
  classical
  have hs : 0 ≤ ∑ a ∈ s.toFinset, ‖a‖ ^ 2 / (2 * |a.im|) := by
    apply Finset.sum_nonneg
    intro a _
    exact div_nonneg (sq_nonneg _) (mul_nonneg (by norm_num) (abs_nonneg _))
  unfold upperClusterRadius
  linarith

lemma upperClusterRadius_gt_ratio (s : Multiset ℂ) {a : ℂ} (ha : a ∈ s) :
    ‖a‖ ^ 2 / (2 * |a.im|) < upperClusterRadius s := by
  classical
  have hs : ‖a‖ ^ 2 / (2 * |a.im|) ≤
      ∑ b ∈ s.toFinset, ‖b‖ ^ 2 / (2 * |b.im|) := by
    apply Finset.single_le_sum (f := fun b : ℂ => ‖b‖ ^ 2 / (2 * |b.im|))
    · intro b _
      exact div_nonneg (sq_nonneg _) (mul_nonneg (by norm_num) (abs_nonneg _))
    · exact Multiset.mem_toFinset.mpr ha
  unfold upperClusterRadius
  linarith

lemma dist_sq_imaginary_center (a : ℂ) (T : ℝ) :
    dist a ((T : ℂ) * Complex.I) ^ 2 = ‖a‖ ^ 2 + T ^ 2 - 2 * T * a.im := by
  rw [dist_eq_norm, Complex.sq_norm, Complex.sq_norm]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_mul, sub_zero, zero_add, add_zero]
  ring

/-- Exact finite spectral separation by the explicit upper circle. -/
theorem upperClusterRadius_separates (s : Multiset ℂ)
    (hreal : ∀ a ∈ s, a.im ≠ 0) {a : ℂ} (ha : a ∈ s) :
    a ∉ sphere ((upperClusterRadius s : ℂ) * Complex.I) (upperClusterRadius s) ∧
      (a ∈ ball ((upperClusterRadius s : ℂ) * Complex.I) (upperClusterRadius s) ↔
        0 < a.im) := by
  have hT := upperClusterRadius_pos s
  have hdist := dist_sq_imaginary_center a (upperClusterRadius s)
  by_cases hi : 0 < a.im
  · have hratio := upperClusterRadius_gt_ratio s ha
    rw [abs_of_pos hi] at hratio
    have hmul := (div_lt_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hi)).1 hratio
    have hlt : dist a ((upperClusterRadius s : ℂ) * Complex.I) < upperClusterRadius s := by
      apply (sq_lt_sq₀ dist_nonneg hT.le).1
      nlinarith [hmul, hdist]
    refine ⟨?_, ⟨fun _ => hi, fun _ => hlt⟩⟩
    intro hs
    have he := Metric.mem_sphere.mp hs
    linarith
  · have him : a.im < 0 := lt_of_le_of_ne (le_of_not_gt hi) (hreal a ha)
    have hprod : upperClusterRadius s * a.im < 0 := mul_neg_of_pos_of_neg hT him
    have hgt : upperClusterRadius s < dist a ((upperClusterRadius s : ℂ) * Complex.I) := by
      apply (sq_lt_sq₀ hT.le dist_nonneg).1
      nlinarith [sq_nonneg ‖a‖, hdist, hprod]
    refine ⟨?_, ⟨?_, fun hp => False.elim (hi hp)⟩⟩
    · intro hs
      have he := Metric.mem_sphere.mp hs
      linarith
    · intro hb
      have hlt : dist a ((upperClusterRadius s : ℂ) * Complex.I) < upperClusterRadius s := hb
      linarith

/-- The disk used by the construction lies strictly in the upper half-plane. -/
lemma upper_circle_ball_subset {T : ℝ} {a : ℂ}
    (ha : a ∈ ball ((T : ℂ) * Complex.I) T) : 0 < a.im := by
  have hnorm : ‖a - (T : ℂ) * Complex.I‖ < T := mem_ball_iff_norm.mp ha
  have hi := Complex.abs_im_le_norm (a - (T : ℂ) * Complex.I)
  have he : (a - (T : ℂ) * Complex.I).im = a.im - T := by simp
  rw [he] at hi
  linarith [neg_le_abs (a.im - T)]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

/-- No diagonalizability assumption is needed to choose the upper cluster. -/
theorem upperClusterTrace_eq_explicit_circle (A : Matrix ι ι ℂ)
    (hreal : ∀ a ∈ A.charpoly.roots, a.im ≠ 0) :
    upperClusterTrace A =
      circleClusterTrace A ((upperClusterRadius A.charpoly.roots : ℂ) * Complex.I)
        (upperClusterRadius A.charpoly.roots) := by
  symm
  exact circleClusterTrace_eq_upperClusterTrace A (upperClusterRadius_pos _).le
    (fun a ha => (upperClusterRadius_separates _ hreal ha).1)
    (fun a ha => (upperClusterRadius_separates _ hreal ha).2)

lemma pencil_roots_im_ne_zero {H Y : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (hY : Y.IsHermitian) (hdet : IsUnit H.det)
    {z : ℂ} (hz : 0 < z.im) :
    ∀ a ∈ (traceDensityPencil H Y z).charpoly.roots, a.im ≠ 0 := by
  intro a ha
  exact pencil_spectrum_im_ne_zero hH hY hdet hz
    (Matrix.mem_spectrum_of_isRoot_charpoly (Polynomial.isRoot_of_mem_roots ha))

/-- At every parameter in the upper half-plane, the source `g(z)` is the
actual normalized trace-resolvent circle integral. The radius is explicit. -/
theorem pencil_upperClusterTrace_eq_circleIntegral {H Y : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (hY : Y.IsHermitian) (hdet : IsUnit H.det)
    {z : ℂ} (hz : 0 < z.im) :
    let R := upperClusterRadius (traceDensityPencil H Y z).charpoly.roots
    upperClusterTrace (traceDensityPencil H Y z) =
      (∮ ζ in C((R : ℂ) * Complex.I, R), pencilTraceIntegrand H Y ζ z) /
        (2 * Real.pi * Complex.I : ℂ) := by
  dsimp only
  rw [pencilTrace_circleIntegral_eq_cluster]
  exact upperClusterTrace_eq_explicit_circle _ (pencil_roots_im_ne_zero hH hY hdet hz)

/-- A separating resolvent contour really exists; its existence is proved
from the finite root data, not supplied as a spectral-projection oracle. -/
theorem exists_pencil_upper_cluster_circle {H Y : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (hY : Y.IsHermitian) (hdet : IsUnit H.det)
    {z : ℂ} (hz : 0 < z.im) :
    ∃ R : ℝ, 0 < R ∧
      (∀ ζ ∈ sphere ((R : ℂ) * Complex.I) R,
        ζ ∉ spectrum ℂ (traceDensityPencil H Y z)) ∧
      upperClusterTrace (traceDensityPencil H Y z) =
        (∮ ζ in C((R : ℂ) * Complex.I, R), pencilTraceIntegrand H Y ζ z) /
          (2 * Real.pi * Complex.I : ℂ) := by
  refine ⟨upperClusterRadius (traceDensityPencil H Y z).charpoly.roots,
    upperClusterRadius_pos _, ?_, pencil_upperClusterTrace_eq_circleIntegral hH hY hdet hz⟩
  intro ζ hζ
  apply circle_not_mem_spectrum_of_root_separation _ _ hζ
  intro a ha
  exact (upperClusterRadius_separates _ (pencil_roots_im_ne_zero hH hY hdet hz) ha).1

end
end CGLMPBounds.Hardy
