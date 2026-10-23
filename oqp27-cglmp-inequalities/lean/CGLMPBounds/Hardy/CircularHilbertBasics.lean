module

public import CGLMPBounds.Defs.CircularHilbert

@[expose] public section


/-! The actual L² Hilbert series: convergence, multiplier and exact norm.
Uses Mathlib's complete Fourier Hilbert basis; no pointwise summability is
asserted. -/

namespace CGLMPBounds.Hardy
open MeasureTheory Matrix
open scoped ComplexConjugate ENNReal lp
noncomputable section
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

@[simp] theorem hilbertMultiplier_zero : hilbertMultiplier 0 = 0 := by
  simp [hilbertMultiplier]

theorem hilbertMultiplier_norm (k : ℤ) :
    ‖hilbertMultiplier k‖ = if k = 0 then 0 else 1 := by
  rcases lt_trichotomy k 0 with hk | rfl | hk
  · simp [hilbertMultiplier, Int.sign_eq_neg_one_of_neg hk, ne_of_lt hk]
  · simp
  · simp [hilbertMultiplier, Int.sign_eq_one_of_pos hk, ne_of_gt hk]

theorem hilbertMultiplier_norm_le (k : ℤ) : ‖hilbertMultiplier k‖ ≤ 1 := by
  rw [hilbertMultiplier_norm]
  split_ifs <;> norm_num

theorem hilbertMultiplier_conj (k : ℤ) : conj (hilbertMultiplier k) = -hilbertMultiplier k := by
  rcases lt_trichotomy k 0 with hk | rfl | hk
  · simp [hilbertMultiplier, Int.sign_eq_neg_one_of_neg hk]
  · simp
  · simp [hilbertMultiplier, Int.sign_eq_one_of_pos hk]

theorem hilbertMultiplier_neg (k : ℤ) : hilbertMultiplier (-k) = -hilbertMultiplier k := by
  simp [hilbertMultiplier, Int.sign_neg]

private def hilbertCoefficients (f : UnitCircle → ℂ) (hf : MemLp f 2 circleMeasure) :
    ℓ²(ℤ, ℂ) :=
  ⟨fun k => hilbertMultiplier k * fourierCoeff f k,
    ((fourierBasis (T := 1)).repr (hf.toLp f)).property.mono' (fun k => by
      rw [fourierBasis_repr, fourierCoeff_congr_ae hf.coeFn_toLp, norm_mul]
      exact (mul_le_mul_of_nonneg_right (hilbertMultiplier_norm_le k) (norm_nonneg _)).trans_eq
        (one_mul _))⟩

private theorem hasSum_hilbertCoefficients (f : UnitCircle → ℂ)
    (hf : MemLp f 2 circleMeasure) :
    HasSum (fun k : ℤ =>
      (hilbertMultiplier k * fourierCoeff f k) • fourierLp (T := 1) 2 k)
      ((fourierBasis (T := 1)).repr.symm (hilbertCoefficients f hf)) := by
  simpa only [hilbertCoefficients, coe_fourierBasis] using
    (fourierBasis (T := 1)).hasSum_repr_symm (hilbertCoefficients f hf)

theorem scalarHilbertLp_summable (f : UnitCircle → ℂ) (hf : MemLp f 2 circleMeasure) :
    Summable (fun k : ℤ =>
      (hilbertMultiplier k * fourierCoeff f k) • fourierLp (T := 1) 2 k) :=
  (hasSum_hilbertCoefficients f hf).summable

private theorem scalarHilbertLp_eq (f : UnitCircle → ℂ) (hf : MemLp f 2 circleMeasure) :
    scalarHilbertLp f = (fourierBasis (T := 1)).repr.symm (hilbertCoefficients f hf) :=
  (hasSum_hilbertCoefficients f hf).tsum_eq

theorem scalarHilbert_fourierCoeff (f : UnitCircle → ℂ)
    (hf : MemLp f 2 circleMeasure) (k : ℤ) :
    fourierCoeff (scalarHilbert f) k = hilbertMultiplier k * fourierCoeff f k := by
  change fourierCoeff (scalarHilbertLp f) k = _
  rw [← fourierBasis_repr, scalarHilbertLp_eq f hf]
  simp [hilbertCoefficients]

theorem scalarHilbert_memLp (f : UnitCircle → ℂ) : MemLp (scalarHilbert f) 2 circleMeasure :=
  Lp.memLp (scalarHilbertLp f)

theorem scalar_fourier_hasSum_norm_sq (f : UnitCircle → ℂ)
    (hf : MemLp f 2 circleMeasure) :
    HasSum (fun k : ℤ => ‖fourierCoeff f k‖ ^ 2) (‖hf.toLp f‖ ^ 2) := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, fourierBasis_repr,
    fourierCoeff_congr_ae hf.coeFn_toLp, LinearIsometryEquiv.norm_map] using
    lp.hasSum_norm (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
      ((fourierBasis (T := 1)).repr (hf.toLp f))

theorem scalarHilbert_norm_sq (f : UnitCircle → ℂ) (hf : MemLp f 2 circleMeasure) :
    ‖scalarHilbertLp f‖ ^ 2 = ‖hf.toLp f‖ ^ 2 - ‖fourierCoeff f 0‖ ^ 2 := by
  have hs := scalar_fourier_hasSum_norm_sq f hf
  have hH : HasSum (fun k : ℤ => ‖hilbertMultiplier k * fourierCoeff f k‖ ^ 2)
      (‖scalarHilbertLp f‖ ^ 2) := by
    simpa only [scalarHilbertLp_eq f hf, LinearIsometryEquiv.norm_map,
      hilbertCoefficients, ENNReal.toReal_ofNat, Real.rpow_two] using
      lp.hasSum_norm (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (hilbertCoefficients f hf)
  have hterm (k : ℤ) : ‖hilbertMultiplier k * fourierCoeff f k‖ ^ 2 =
      if k = 0 then 0 else ‖fourierCoeff f k‖ ^ 2 := by
    rw [norm_mul, hilbertMultiplier_norm]
    split_ifs <;> simp
  simp_rw [hterm] at hH
  have hsplit := hs.summable.tsum_eq_add_tsum_ite 0
  rw [hs.tsum_eq, hH.tsum_eq] at hsplit
  linarith

theorem scalarHilbert_norm_le (f : UnitCircle → ℂ) (hf : MemLp f 2 circleMeasure) :
    ‖scalarHilbertLp f‖ ≤ ‖hf.toLp f‖ := by
  have h := scalarHilbert_norm_sq f hf
  nlinarith [norm_nonneg (scalarHilbertLp f), norm_nonneg (hf.toLp f),
    sq_nonneg ‖fourierCoeff f 0‖]

end
end CGLMPBounds.Hardy
