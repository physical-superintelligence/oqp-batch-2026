module

public import ThreeCopyQutritWerner.NuclearTrace

@[expose] public section


/-!
# Exterior-square control without an SVD dependency

The trace identity (Tr Y)² − Tr(Y²) = 2 Tr(compound₂ Y), followed by finite
Cauchy--Schwarz, is sufficient for the direction of the singular-value identity
needed in Wu--Zou Lemma 5.1. A compound of a unitary is completed by the identity
on symmetric ordered pairs, giving a genuine ambient unitary trace test.

The resulting reduced-transition bound is unconditional matrix algebra. It
does not include the separate sharp complementary partial-trace inequality.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace ThreeCopyQutritWerner

/-- The compound identity is the antisymmetric-pair projection. -/
theorem zeroReserveCompound_one_mul {m n : Type*} [Fintype m] [DecidableEq m]
    (X : Matrix m n ℂ) :
    zeroReserveCompound (1 : Matrix m m ℂ) * zeroReserveCompound X =
      zeroReserveCompound X := by
  rw [← zeroReserveCompound_mul, Matrix.one_mul]

theorem zeroReserveCompound_mul_one {m n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix m n ℂ) :
    zeroReserveCompound X * zeroReserveCompound (1 : Matrix n n ℂ) =
      zeroReserveCompound X := by
  rw [← zeroReserveCompound_mul, Matrix.mul_one]

/-- Extend the exterior-square unitary by the identity on symmetric ordered pairs. -/
def nuclearTraceCompoundUnitary {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix n n ℂ) : Matrix (n × n) (n × n) ℂ :=
  zeroReserveCompound U + (1 - zeroReserveCompound (1 : Matrix n n ℂ))

/-- The extension is an actual unitary matrix in the ambient ordered-pair space. -/
theorem nuclearTraceCompoundUnitary_isometry {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix n n ℂ) (hU : Uᴴ * U = 1) :
    (nuclearTraceCompoundUnitary U)ᴴ * nuclearTraceCompoundUnitary U = 1 := by
  have hp : (zeroReserveCompound (1 : Matrix n n ℂ))ᴴ = zeroReserveCompound 1 := by
    rw [← zeroReserveCompound_conjTranspose, Matrix.conjTranspose_one]
  have hprod : (zeroReserveCompound U)ᴴ * zeroReserveCompound U = zeroReserveCompound 1 := by
    rw [← zeroReserveCompound_conjTranspose, ← zeroReserveCompound_mul, hU]
  have hc : (zeroReserveCompound U)ᴴ * zeroReserveCompound (1 : Matrix n n ℂ) =
      (zeroReserveCompound U)ᴴ := by
    rw [← zeroReserveCompound_conjTranspose, zeroReserveCompound_mul_one]
  simp only [nuclearTraceCompoundUnitary, Matrix.conjTranspose_add, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_one, hp, Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul,
    Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hprod, hc,
    zeroReserveCompound_one_mul]
  abel

/-- The symmetric complement added to the test does not act on any compound. -/
theorem nuclearTraceCompoundUnitary_test {n : Type*} [Fintype n] [DecidableEq n]
    (U X : Matrix n n ℂ) :
    (nuclearTraceCompoundUnitary U)ᴴ * zeroReserveCompound X =
      zeroReserveCompound (Uᴴ * X) := by
  have hp : (zeroReserveCompound (1 : Matrix n n ℂ))ᴴ = zeroReserveCompound 1 := by
    rw [← zeroReserveCompound_conjTranspose, Matrix.conjTranspose_one]
  simp only [nuclearTraceCompoundUnitary, Matrix.conjTranspose_add, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_one, hp, Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul,
    zeroReserveCompound_one_mul, sub_self, add_zero,
    ← zeroReserveCompound_conjTranspose, ← zeroReserveCompound_mul]

/-- Exact character identity of the second exterior power. -/
theorem zeroReserveCompound_trace {n : Type*} [Fintype n] (X : Matrix n n ℂ) :
    2 * (zeroReserveCompound X).trace = X.trace ^ 2 - (X * X).trace := by
  simp only [Matrix.trace, Matrix.diag_apply, zeroReserveCompound,
    Fintype.sum_prod_type, Matrix.mul_apply, Finset.sum_sub_distrib, Finset.sum_div]
  rw [show (∑ i, X i i) ^ 2 = ∑ i, ∑ j, (X i i) * (X j j) by
    simp only [pow_two, Finset.sum_mul_sum]]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem nuclearTrace_frobSq_conjTranspose {m n : Type*}
    [Fintype m] [Fintype n] (X : Matrix m n ℂ) : frobSq Xᴴ = frobSq X := by
  simp only [frobSq, Matrix.conjTranspose_apply, Complex.star_def, Complex.normSq_conj]
  exact Finset.sum_comm

/-- The potentially non-Hermitian square trace is controlled by the literal squared Frobenius norm. -/
theorem nuclearTrace_square_trace_le {n : Type*} [Fintype n] (X : Matrix n n ℂ) :
    ‖(X * X).trace‖ ≤ frobSq X := by
  have h := nuclearTrace_pair_normSq_le Xᴴ X
  rw [Matrix.conjTranspose_conjTranspose, nuclearTrace_frobSq_conjTranspose,
    Complex.normSq_eq_norm_sq] at h
  have hn := frobSq_nonneg X
  have ht := norm_nonneg ((X * X).trace)
  nlinarith

/-- Every unitary trace test is controlled by the Frobenius and compound norms. -/
theorem nuclearTrace_test_sq_le_compound {n : Type*} [Fintype n] [DecidableEq n]
    (X U : Matrix n n ℂ) (hU : Uᴴ * U = 1) :
    ‖(Uᴴ * X).trace‖ ^ 2 ≤ frobSq X + 2 * nuclearTrace (zeroReserveCompound X) := by
  have hUU : U * Uᴴ = 1 := mul_eq_one_comm.mp hU
  have hf : frobSq (Uᴴ * X) = frobSq X :=
    nuclearTrace_frobSq_isometry_mul Uᴴ X (by simpa using hUU)
  have hc := nuclearTrace_test_le (zeroReserveCompound X)
    (nuclearTraceCompoundUnitary U) (nuclearTraceCompoundUnitary_isometry U hU)
  rw [nuclearTraceCompoundUnitary_test] at hc
  have he : (Uᴴ * X).trace ^ 2 = (Uᴴ * X * (Uᴴ * X)).trace +
      2 * (zeroReserveCompound (Uᴴ * X)).trace := by
    have h := zeroReserveCompound_trace (Uᴴ * X)
    linear_combination -h
  calc
    ‖(Uᴴ * X).trace‖ ^ 2 = ‖(Uᴴ * X).trace ^ 2‖ := (norm_pow _ _).symm
    _ = ‖(Uᴴ * X * (Uᴴ * X)).trace +
        2 * (zeroReserveCompound (Uᴴ * X)).trace‖ := by rw [he]
    _ ≤ ‖(Uᴴ * X * (Uᴴ * X)).trace‖ +
        ‖2 * (zeroReserveCompound (Uᴴ * X)).trace‖ := norm_add_le _ _
    _ ≤ frobSq X + 2 * nuclearTrace (zeroReserveCompound X) := by
      have hs := nuclearTrace_square_trace_le (Uᴴ * X)
      rw [hf] at hs
      rw [norm_mul, Complex.norm_two]
      linarith

/-- The needed direction of the second-compound singular-value identity, proved without an SVD. -/
theorem nuclearTrace_sq_sub_frobSq_le_compound {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) :
    nuclearTrace X ^ 2 - frobSq X ≤ 2 * nuclearTrace (zeroReserveCompound X) := by
  let b : ℝ := frobSq X + 2 * nuclearTrace (zeroReserveCompound X)
  have hb : 0 ≤ b := add_nonneg (frobSq_nonneg _) (mul_nonneg (by norm_num) (nuclearTrace_nonneg _))
  have hsup : nuclearTrace X ≤ Real.sqrt b := by
    apply csSup_le (nuclearTraceTests_nonempty X)
    rintro r ⟨U, hU, rfl⟩
    have h := nuclearTrace_test_sq_le_compound X U hU
    have hs := Real.sq_sqrt hb
    have hn := Real.sqrt_nonneg b
    have ht := norm_nonneg ((Uᴴ * X).trace)
    change ‖(Uᴴ * X).trace‖ ^ 2 ≤ b at h
    nlinarith
  have hn := nuclearTrace_nonneg X
  have hs := Real.sq_sqrt hb
  have hroot := Real.sqrt_nonneg b
  dsimp [b] at hs
  nlinarith

/-- Wu--Zou's reduced-transition exterior-square estimate, before normalizing the two rays. -/
theorem nuclearTrace_transition_defect_le {n k : Type*}
    [Fintype n] [Fintype k] [DecidableEq n]
    (A B : Matrix n k ℂ) :
    nuclearTrace (A * Bᴴ) ^ 2 - frobSq (A * Bᴴ) ≤
      Real.sqrt ((frobSq A ^ 2 - frobSq (Aᴴ * A)) *
        (frobSq B ^ 2 - frobSq (Bᴴ * B))) := by
  calc
    nuclearTrace (A * Bᴴ) ^ 2 - frobSq (A * Bᴴ) ≤
        2 * nuclearTrace (zeroReserveCompound (A * Bᴴ)) :=
      nuclearTrace_sq_sub_frobSq_le_compound _
    _ ≤ 2 * Real.sqrt (frobSq (zeroReserveCompound A) *
        frobSq (zeroReserveCompound B)) := by
      have h := nuclearTrace_compound_mul_conjTranspose_le A B
      linarith
    _ = _ := by
      rw [← zeroReserveCompound_frobSq A, ← zeroReserveCompound_frobSq B]
      rw [show (2 * frobSq (zeroReserveCompound A)) *
        (2 * frobSq (zeroReserveCompound B)) =
          4 * (frobSq (zeroReserveCompound A) * frobSq (zeroReserveCompound B)) by ring]
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
      rw [show Real.sqrt (4 : ℝ) = 2 from
        (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)]

/-- The unit-ray form used in the rank-two reserve estimate. -/
theorem nuclearTrace_transition_defect_le_unit {n k : Type*}
    [Fintype n] [Fintype k] [DecidableEq n]
    (A B : Matrix n k ℂ) (hA : frobSq A = 1) (hB : frobSq B = 1) :
    nuclearTrace (A * Bᴴ) ^ 2 - frobSq (A * Bᴴ) ≤
      Real.sqrt ((1 - frobSq (Aᴴ * A)) * (1 - frobSq (Bᴴ * B))) := by
  simpa only [hA, hB, one_pow] using nuclearTrace_transition_defect_le A B

end ThreeCopyQutritWerner
