module

public import ThreeCopyQutritWerner.CoherentShadowCombination
public import ThreeCopyQutritWerner.Identities

@[expose] public section


/-!
# Scalar logical compression cancels the overlap terms

The quantitative floor and coherent-pencil equality follow for actual balanced
two-column factors with Y†X scalar. Later modules relate the first term to the
singularGapSq definition and derive common physical thinness.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace ThreeCopyQutritWerner

/-- The original positive-source overlap is the logical cross-Gram norm. -/
theorem coherentShadow_source_overlap {m n : Type*} [Fintype m] [Fintype n]
    (X Y : Matrix m n ℂ) :
    (hsInner (X * Xᴴ) (Y * Yᴴ)).re = frobSq (Yᴴ * X) := by
  have h := congrArg Complex.re (jointShadow_frobSq_cross_gram Yᴴ Xᴴ)
  simp only [Matrix.conjTranspose_conjTranspose, Complex.ofReal_re] at h
  rw [hsInner_eq_trace, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.trace_mul_comm]
  exact h.symm

variable {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    [DecidableEq a] [DecidableEq b] [DecidableEq c]

/-- The scalar 2×2 compression gives exactly the QR4 cancellation. -/
theorem coherentShadow_scalar_overlap_cancel
    (X Y : Matrix (a × b × c) (Fin 2) ℂ) (κ : ℂ)
    (hκ : Yᴴ * X = κ • (1 : Matrix (Fin 2) (Fin 2) ℂ)) :
    -(hsInner (X * Xᴴ) (Y * Yᴴ)).re / 12 + invT (X * Yᴴ) / 24 = 0 := by
  have hh : frobSq (Yᴴ * X) = 2 * Complex.normSq κ := by
    rw [hκ, frobSq_smul]
    norm_num [frobSq, Fin.sum_univ_two, Matrix.one_apply] <;> ring
  have ht : invT (X * Yᴴ) = 4 * Complex.normSq κ := by
    rw [invT, Matrix.trace_mul_comm, hκ, Matrix.trace_smul, Matrix.trace_one]
    norm_num [smul_eq_mul, Complex.normSq_mul, Complex.normSq_ofReal] <;> ring
  rw [coherentShadow_source_overlap, hh, ht]
  ring

/-- The balanced first term is nonnegative by the actual rank-two trace bound. -/
theorem coherentShadow_gap_nonneg (X Y : Matrix (a × b × c) (Fin 2) ℂ)
    (hG : Xᴴ * X = Yᴴ * Y) :
    0 ≤ 2 * invN (X * Yᴴ) - frobSq X ^ 2 := by
  have hr : (X * Xᴴ).rank ≤ 2 :=
    (Matrix.rank_mul_le_left _ _).trans (by simpa using Matrix.rank_le_card_width X)
  have ht := normSq_trace_le_two_mul_of_rank_le_two (X * Xᴴ) hr
  change Complex.normSq (X * Xᴴ).trace ≤ 2 * frobSq (X * Xᴴ) at ht
  rw [jointShadow_trace_source, Complex.normSq_ofReal,
    (jointShadow_balanced_norms X Y hG).1] at ht
  change 0 ≤ 2 * frobSq (X * Yᴴ) - frobSq X ^ 2
  nlinarith

/-- The quantitative scalar-compression floor, with both nonnegative reserves
and the actual common marginal slack still retained. -/
theorem coherentShadow_scalar_floor
    (X Y : Matrix (a × b × c) (Fin 2) ℂ)
    (hn : 2 ≤ Fintype.card (a × b × c)) (hG : Xᴴ * X = Yᴴ * Y)
    (κ : ℂ) (hκ : Yᴴ * X = κ • (1 : Matrix (Fin 2) (Fin 2) ℂ)) :
    (2 * invN (X * Yᴴ) - frobSq X ^ 2) / 6 +
      (Real.sqrt (zeroReserve (X * Xᴴ)) - Real.sqrt (zeroReserve (Y * Yᴴ))) ^ 2 / 6 +
      (2 * jointShadowMarginalDefect X Y - invB (X * Xᴴ - Y * Yᴴ)) / 24 ≤
        endpointEnergy (X * Yᴴ) := by
  have h := coherentShadow_endpoint_lower_bound X Y hn hG
  have hc := coherentShadow_scalar_overlap_cancel X Y κ hκ
  unfold coherentShadowFloor at h
  linarith

/-- The scalar-compression quantitative bound in actual balanced Gram invariants. -/
theorem coherentShadow_scalar_quantitative_bound
    (X Y : Matrix (a × b × c) (Fin 2) ℂ)
    (hn : 2 ≤ Fintype.card (a × b × c)) (hG : Xᴴ * X = Yᴴ * Y)
    (κ : ℂ) (hκ : Yᴴ * X = κ • (1 : Matrix (Fin 2) (Fin 2) ℂ)) :
    (2 * invN (X * Yᴴ) - frobSq X ^ 2) / 6 ≤ endpointEnergy (X * Yᴴ) := by
  have h := coherentShadow_scalar_floor X Y hn hG κ hκ
  have hs := jointShadow_logical_slack_nonneg X Y
  have hsq := sq_nonneg (Real.sqrt (zeroReserve (X * Xᴴ)) -
    Real.sqrt (zeroReserve (Y * Yᴴ)))
  linarith

/-- Actual scalar-compression sources have nonnegative endpoint energy. -/
theorem coherentShadow_scalar_nonneg
    (X Y : Matrix (a × b × c) (Fin 2) ℂ)
    (hn : 2 ≤ Fintype.card (a × b × c)) (hG : Xᴴ * X = Yᴴ * Y)
    (κ : ℂ) (hκ : Yᴴ * X = κ • (1 : Matrix (Fin 2) (Fin 2) ℂ)) :
    0 ≤ endpointEnergy (X * Yᴴ) := by
  have h := coherentShadow_scalar_quantitative_bound X Y hn hG κ hκ
  have hg := coherentShadow_gap_nonneg X Y hG
  linarith

end ThreeCopyQutritWerner
