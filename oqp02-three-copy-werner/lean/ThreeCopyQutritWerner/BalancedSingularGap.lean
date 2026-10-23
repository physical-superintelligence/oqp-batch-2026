module

public import ThreeCopyQutritWerner.BalancedScalarFactors
public import ThreeCopyQutritWerner.AppendixCInputs
public import Mathlib.Analysis.Matrix.PosDef

@[expose] public section


/-!
# The singular-gap formula in balanced two-column coordinates

Two 2×2 trace/determinant identities identify the manuscript's polynomial
singularGapSq with the actual balanced Gram gap. Positivity of the Gram fixes
the sign of the square root, including the rank-deficient boundary.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace ThreeCopyQutritWerner

/-- The elementary degree-two trace identity in two dimensions. -/
theorem balancedGram_trace_square (G : Matrix (Fin 2) (Fin 2) ℂ) :
    (G * G).trace = G.trace ^ 2 - 2 * G.det := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.det_fin_two]
  ring

/-- The degree-four trace identity, with no spectral or Hermitian assumptions. -/
theorem balancedGram_trace_fourth (G : Matrix (Fin 2) (Fin 2) ℂ) :
    ((G * G) * (G * G)).trace = (G * G).trace ^ 2 - 2 * G.det ^ 2 := by
  rw [balancedGram_trace_square (G * G), Matrix.det_mul]
  ring

/-- The physical fourth singular moment is the fourth logical Gram trace. -/
theorem balancedFactors_fourth_moment {m n : Type*} [Fintype m] [Fintype n]
    (X Y : Matrix m n ℂ) (hG : Xᴴ * X = Yᴴ * Y) :
    (frobSq ((X * Yᴴ)ᴴ * (X * Yᴴ)) : ℂ) =
      (((Xᴴ * X) * (Xᴴ * X)) * ((Xᴴ * X) * (Xᴴ * X))).trace := by
  let G := Xᴴ * X
  have hGY : Yᴴ * Y = G := hG.symm
  have hGh : Gᴴ = G := by simp [G]
  have hM : (X * Yᴴ)ᴴ * (X * Yᴴ) = Y * G * Yᴴ := by
    simp only [G, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc]
  have hMh : (Y * G * Yᴴ)ᴴ = Y * G * Yᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hGh, Matrix.mul_assoc]
  rw [hM, ofReal_frobSq_eq_trace, hMh]
  calc
    ((Y * G * Yᴴ) * (Y * G * Yᴴ)).trace =
        (Y * ((G * (Yᴴ * Y) * G) * Yᴴ)).trace := by
      simp only [Matrix.mul_assoc]
    _ = (((G * (Yᴴ * Y) * G) * Yᴴ) * Y).trace := Matrix.trace_mul_comm _ _
    _ = ((G * (Yᴴ * Y) * G) * (Yᴴ * Y)).trace := by rw [Matrix.mul_assoc]
    _ = ((G * G) * (G * G)).trace := by rw [hGY]; simp only [Matrix.mul_assoc]

/-- Both real scalar identities come from the actual positive 2×2 Gram. -/
theorem balancedFactors_gap_invariants {m : Type*} [Fintype m]
    (X Y : Matrix m (Fin 2) ℂ) (hG : Xᴴ * X = Yᴴ * Y) :
    0 ≤ (Xᴴ * X).det.re ∧
      frobSq (X * Yᴴ) = frobSq X ^ 2 - 2 * (Xᴴ * X).det.re ∧
      (frobSq (X * Yᴴ) ^ 2 - frobSq ((X * Yᴴ)ᴴ * (X * Yᴴ))) / 2 =
        (Xᴴ * X).det.re ^ 2 := by
  let G := Xᴴ * X
  have hd := Complex.nonneg_iff.mp (Matrix.posSemidef_conjTranspose_mul_self X).det_nonneg
  have hdcast : ((G.det.re : ℝ) : ℂ) = G.det := by
    apply Complex.ext
    · simp
    · simpa only [Complex.ofReal_im] using hd.2
  have htr : G.trace = (frobSq X : ℂ) := (ofReal_frobSq_eq_trace X).symm
  have hn : (G * G).trace = (frobSq (X * Yᴴ) : ℂ) := by
    rw [jointShadow_frobSq_cross_gram, ← hG]
  have h2 := balancedGram_trace_square G
  have h4 := balancedGram_trace_fourth G
  rw [htr, hn, ← hdcast] at h2
  have h2r : frobSq (X * Yᴴ) = frobSq X ^ 2 - 2 * G.det.re := by
    exact_mod_cast h2
  rw [← balancedFactors_fourth_moment X Y hG, hn, ← hdcast] at h4
  have h4r : frobSq ((X * Yᴴ)ᴴ * (X * Yᴴ)) =
      frobSq (X * Yᴴ) ^ 2 - 2 * G.det.re ^ 2 := by
    exact_mod_cast h4
  exact ⟨hd.1, h2r, by linarith⟩

/-- Exact equality with the existing singular-gap definition. -/
theorem singularGapSq_balanced_factors
    {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    (X Y : Matrix (a × b × c) (Fin 2) ℂ) (hG : Xᴴ * X = Yᴴ * Y) :
    singularGapSq (X * Yᴴ) = 2 * invN (X * Yᴴ) - frobSq X ^ 2 := by
  obtain ⟨hd, h2, h4⟩ := balancedFactors_gap_invariants X Y hG
  rw [singularGapSq, h4, Real.sqrt_sq hd]
  unfold invN
  linarith

/-- The quantitative inequality from AppC-1, for actual rank-two scalar-idempotent
matrices. The common-site equality classification is a separate obligation. -/
theorem singularGapSq_le_six_endpoint_of_scalar_square
    {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    [DecidableEq a] [DecidableEq b] [DecidableEq c]
    (C : Matrix (a × b × c) (a × b × c) ℂ)
    (hr : C.rank = 2) (κ : ℂ) (hκ : C * C = κ • C) :
    singularGapSq C / 6 ≤ endpointEnergy C := by
  have hn : 2 ≤ Fintype.card (a × b × c) := by
    simpa only [hr] using Matrix.rank_le_card_width C
  obtain ⟨X, Y, hC, hG, hXY⟩ := exists_balanced_scalar_factors C hr κ hκ
  rw [hC, singularGapSq_balanced_factors X Y hG]
  exact coherentShadow_scalar_quantitative_bound X Y hn hG κ hXY

end ThreeCopyQutritWerner
