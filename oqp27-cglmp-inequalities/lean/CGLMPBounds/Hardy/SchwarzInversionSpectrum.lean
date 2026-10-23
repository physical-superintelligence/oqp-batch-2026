module

public import CGLMPBounds.Hardy.SchwarzSafeNegativeContour
public import CGLMPBounds.Hardy.SchwarzInversionGeometry
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas

@[expose] public section


/-! The actual spectrum and matrix algebra needed by C.7 inversion. The safe
negative H-inverse disk maps to a disk selecting exactly the negative roots
of H, without a generic root-selection assumption in the final existence
statement. The pointwise matrix substitution keeps all matrix factors in
order. It is distinct from the still-required matrix contour transport. -/

open Complex Metric Set
open scoped Matrix.Norms.Operator

namespace CGLMPBounds.Hardy
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

lemma inverse_mem_matrix_spectrum_iff {H : Matrix ι ι ℂ}
    (hdet : IsUnit H.det) (a : ℂ) :
    a⁻¹ ∈ spectrum ℂ H⁻¹ ↔ a ∈ spectrum ℂ H := by
  have hH : IsUnit H := (Matrix.isUnit_iff_isUnit_det H).mpr hdet
  simpa only [Matrix.coe_units_inv, IsUnit.unit_spec] using
    (spectrum.inv₀_mem_inv_iff (R := ℂ) (a := hH.unit) (r := a))

lemma inverse_mem_matrix_roots_iff {H : Matrix ι ι ℂ}
    (hdet : IsUnit H.det) (a : ℂ) :
    a⁻¹ ∈ H⁻¹.charpoly.roots ↔ a ∈ H.charpoly.roots := by
  rw [Polynomial.mem_roots H⁻¹.charpoly_monic.ne_zero,
    Polynomial.mem_roots H.charpoly_monic.ne_zero,
    ← Matrix.mem_spectrum_iff_isRoot_charpoly,
    ← Matrix.mem_spectrum_iff_isRoot_charpoly]
  exact inverse_mem_matrix_spectrum_iff hdet a

lemma inverse_re_neg_iff {a : ℂ} (ha : a ≠ 0) : (a⁻¹).re < 0 ↔ a.re < 0 := by
  have hn : 0 < Complex.normSq a := by
    rw [← Complex.sq_norm]
    exact sq_pos_of_pos (norm_pos_iff.mpr ha)
  rw [Complex.inv_re, div_lt_iff₀ hn, zero_mul]

/-- The actual inverted safe circle selects exactly the negative roots of H.
The original H-inverse safe radius and all normalization data are retained. -/
theorem exists_inverted_negative_matrix_circle {H : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (hdet : IsUnit H.det) :
    let R := negativeClusterRadius H⁻¹.charpoly.roots
    ∃ r : ℝ, 0 < r ∧ r < R ∧
      (0 : ℂ) ∉ closedBall (-(R : ℂ)) r ∧
      (0 : ℂ) ∉ closedBall (((-R / (R ^ 2 - r ^ 2)) : ℝ) : ℂ)
        (r / (R ^ 2 - r ^ 2)) ∧
      ∀ a ∈ H.charpoly.roots,
        a ∉ sphere (((-R / (R ^ 2 - r ^ 2)) : ℝ) : ℂ) (r / (R ^ 2 - r ^ 2)) ∧
        (a ∈ ball (((-R / (R ^ 2 - r ^ 2)) : ℝ) : ℂ) (r / (R ^ 2 - r ^ 2)) ↔
          a.re < 0) := by
  let R := negativeClusterRadius H⁻¹.charpoly.roots
  obtain ⟨r, hr0, hrR, hzero, hselect, _⟩ := exists_safe_negative_inverse_circle hH hdet
  have hΔ : 0 < (-R) ^ 2 - r ^ 2 := by
    have hR0 : 0 < R := negativeClusterRadius_pos _
    nlinarith
  refine ⟨r, hr0, hrR, hzero, ?_, ?_⟩
  · simpa only [neg_sq] using zero_not_mem_inverse_real_disk hr0.le hΔ
  · intro a ha
    have ha0 : a ≠ 0 := by
      intro he
      exact (spectrum.zero_notMem ℂ ((Matrix.isUnit_iff_isUnit_det H).mpr hdet))
        (he ▸ Matrix.mem_spectrum_of_isRoot_charpoly (Polynomial.isRoot_of_mem_roots ha))
    have hai : a⁻¹ ∈ H⁻¹.charpoly.roots := (inverse_mem_matrix_roots_iff hdet a).mpr ha
    have hsphere := inverse_mem_real_sphere_iff hr0.le hΔ ha0
    have hball := inverse_mem_real_ball_iff hr0.le hΔ ha0
    simp only [neg_sq, Complex.ofReal_neg] at hsphere hball
    refine ⟨fun hs => (hselect a⁻¹ hai).1 (hsphere.mpr hs), ?_⟩
    exact hball.symm.trans ((hselect a⁻¹ hai).2.trans (inverse_re_neg_iff ha0))

/-- Pointwise matrix substitution, before integrating. It remains valid at
poles under the shared totalized inverse convention; the actual contours
separately avoid those poles. -/
lemma inverse_pencil_eq_inverse_coordinate_resolvent (H : Matrix ι ι ℂ)
    {ζ : ℂ} (hζ : ζ ≠ 0) :
    Ring.inverse (ζ • H - 1) = (-ζ⁻¹) • resolvent H ζ⁻¹ := by
  have hu : IsUnit (-ζ) := (neg_ne_zero.mpr hζ).isUnit
  have hfac : ζ • H - 1 =
      algebraMap ℂ (Matrix ι ι ℂ) (-ζ) *
        (algebraMap ℂ (Matrix ι ι ℂ) ζ⁻¹ - H) := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      smul_mul_assoc, Matrix.one_mul, smul_sub, smul_smul]
    simp [hζ, neg_smul, sub_eq_add_neg, add_comm]
  rw [hfac, Ring.inverse_mul (Or.inl (hu.map (algebraMap ℂ (Matrix ι ι ℂ)))),
    ← hu.map_ringInverse (algebraMap ℂ (Matrix ι ι ℂ)), Ring.inverse_eq_inv,
    Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
    mul_smul_comm, Matrix.mul_one, inv_neg, resolvent,
    Algebra.algebraMap_eq_smul_one]

lemma inverse_pencil_power_trace (H Y : Matrix ι ι ℂ)
    {ζ : ℂ} (hζ : ζ ≠ 0) (n : ℕ) :
    Matrix.trace ((Ring.inverse (ζ • H - 1) * Y) ^ n) =
      (-ζ⁻¹) ^ n * Matrix.trace ((resolvent H ζ⁻¹ * Y) ^ n) := by
  rw [inverse_pencil_eq_inverse_coordinate_resolvent H hζ,
    smul_mul_assoc, smul_pow, Matrix.trace_smul, smul_eq_mul]

end
end CGLMPBounds.Hardy
