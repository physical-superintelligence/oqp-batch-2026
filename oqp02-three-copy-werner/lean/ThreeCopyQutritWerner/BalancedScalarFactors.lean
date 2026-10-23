module

public import ThreeCopyQutritWerner.CoherentShadowScalar
public import ThreeCopyQutritWerner.TwoCutFactor
public import ThreeCopyQutritWerner.ZeroRelations

@[expose] public section


/-!
# Actual balanced two-column factors for scalar-idempotent matrices

The factors are constructed from the existing rank-at-most-two decomposition.
Rank two supplies ordinary left/right inverses, so the scalar logical compression
is a consequence of C²=κC and is not an additional mathematical input.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace ThreeCopyQutritWerner

/-- A literal matrix with the two specified columns. -/
def balancedTwoColumns {n : Type*} (u v : n → ℂ) : Matrix n (Fin 2) ℂ :=
  fun i j => ![u i, v i] j

/-- The two-column product is the actual sum of the two outer products. -/
theorem balancedTwoColumns_mul {n : Type*} [Fintype n]
    (u v x y : n → ℂ) :
    balancedTwoColumns u v * (balancedTwoColumns x y)ᴴ = ketBra u x + ketBra v y := by
  ext i j
  simp [balancedTwoColumns, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.conjTranspose_apply, ketBra]

/-- The logical Gram consists of the original vector inner products. -/
theorem balancedTwoColumns_gram {n : Type*} [Fintype n]
    (u v : n → ℂ) :
    (balancedTwoColumns u v)ᴴ * balancedTwoColumns u v =
      !![braket u u, braket u v; braket v u, braket v v] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [balancedTwoColumns, Matrix.mul_apply, Matrix.conjTranspose_apply, braket]

/-- Every actual rank-at-most-two matrix has equal logical Gram factors. -/
theorem exists_balanced_twoColumn_factors {n : Type*} [Fintype n] [DecidableEq n]
    (C : Matrix n n ℂ) (hr : C.rank ≤ 2) :
    ∃ X Y : Matrix n (Fin 2) ℂ, C = X * Yᴴ ∧ Xᴴ * X = Yᴴ * Y := by
  obtain ⟨u, v, x, y, hC, hu, hv, huv⟩ := exists_balanced_ketBra C hr
  refine ⟨balancedTwoColumns u v, balancedTwoColumns x y, ?_, ?_⟩
  · rw [balancedTwoColumns_mul]
    exact hC
  · rw [balancedTwoColumns_gram, balancedTwoColumns_gram]
    have hvu : braket v u = braket y x := by
      rw [← conj_braket u v, ← conj_braket x y, huv]
    rw [braket_self u, braket_self v, braket_self x, braket_self y, hu, hv, huv, hvu]

/-- For rank two the scalar compression follows from the original square equation. -/
theorem balancedFactors_scalar_compression {n : Type*} [Fintype n]
    (X Y : Matrix n (Fin 2) ℂ) (hr : (X * Yᴴ).rank = 2)
    (κ : ℂ) (hκ : (X * Yᴴ) * (X * Yᴴ) = κ • (X * Yᴴ)) :
    Yᴴ * X = κ • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  obtain ⟨hX, hY⟩ := rank_eq_two_of_mul X Yᴴ hr
  obtain ⟨L, hL⟩ := exists_left_inverse_of_rank_eq_two X hX
  obtain ⟨R, hR⟩ := exists_right_inverse_of_rank_eq_two Yᴴ hY
  exact compress_eq_smul_of_sq X Yᴴ L R hL hR κ hκ

/-- All factor conditions required by the shadow argument are now constructed. -/
theorem exists_balanced_scalar_factors {n : Type*} [Fintype n] [DecidableEq n]
    (C : Matrix n n ℂ) (hr : C.rank = 2) (κ : ℂ) (hκ : C * C = κ • C) :
    ∃ X Y : Matrix n (Fin 2) ℂ,
      C = X * Yᴴ ∧ Xᴴ * X = Yᴴ * Y ∧
        Yᴴ * X = κ • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  obtain ⟨X, Y, hC, hG⟩ := exists_balanced_twoColumn_factors C hr.le
  refine ⟨X, Y, hC, hG, balancedFactors_scalar_compression X Y ?_ κ ?_⟩
  · simpa only [← hC] using hr
  · simpa only [← hC] using hκ

/-- The scalar-idempotent branch has nonnegative endpoint energy, with no
supplied factorization or shadow inequality premise. -/
theorem endpointEnergy_nonneg_of_rank_two_scalar_square
    {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    [DecidableEq a] [DecidableEq b] [DecidableEq c]
    (C : Matrix (a × b × c) (a × b × c) ℂ)
    (hr : C.rank = 2) (κ : ℂ) (hκ : C * C = κ • C) :
    0 ≤ endpointEnergy C := by
  have hn : 2 ≤ Fintype.card (a × b × c) := by
    simpa only [hr] using Matrix.rank_le_card_width C
  obtain ⟨X, Y, hC, hG, hXY⟩ := exists_balanced_scalar_factors C hr κ hκ
  rw [hC]
  exact coherentShadow_scalar_nonneg X Y hn hG κ hXY

end ThreeCopyQutritWerner
