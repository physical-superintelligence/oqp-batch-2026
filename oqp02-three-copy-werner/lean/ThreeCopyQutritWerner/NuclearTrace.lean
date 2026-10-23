module

public import ThreeCopyQutritWerner.ZeroReserveCompound
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

@[expose] public section


/-!
# A variational nuclear trace norm and its Hilbert--Schmidt factor bound

The definition is the literal supremum of |Tr(U†X)| over square unitary matrices.
This is the usual variational characterization of the nuclear trace norm; no
saved eigenvalues or numerical norm are used. This file proves directly that
the supremum is finite and that ||AB†||₁ ≤ ||A||F ||B||F.

The singular-value sum identity and the sharp complementary partial-trace
inequality are separate obligations, not hypotheses or conclusions here.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace ThreeCopyQutritWerner

/-- Finite Hilbert--Schmidt Cauchy--Schwarz, with the exact trace and conjugation. -/
theorem nuclearTrace_pair_normSq_le {m n : Type*} [Fintype m] [Fintype n]
    (A B : Matrix m n ℂ) :
    Complex.normSq (Aᴴ * B).trace ≤ frobSq A * frobSq B := by
  have ht : (Aᴴ * B).trace = ∑ p : m × n, conj (A p.1 p.2) * B p.1 p.2 := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Complex.star_def, Fintype.sum_prod_type]
    exact Finset.sum_comm
  rw [ht]
  have h := normSq_sum_mul_le Finset.univ
    (fun p : m × n => conj (A p.1 p.2)) (fun p : m × n => B p.1 p.2)
  simpa only [Complex.normSq_conj, Fintype.sum_prod_type, frobSq] using h

/-- Left multiplication by an actual isometry preserves Frobenius norm. -/
theorem nuclearTrace_frobSq_isometry_mul {m n k : Type*}
    [Fintype m] [Fintype n] [Fintype k] [DecidableEq n]
    (U : Matrix m n ℂ) (A : Matrix n k ℂ) (hU : Uᴴ * U = 1) :
    frobSq (U * A) = frobSq A := by
  apply Complex.ofReal_injective
  rw [ofReal_frobSq_eq_trace, ofReal_frobSq_eq_trace, Matrix.conjTranspose_mul]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ U A, hU, Matrix.one_mul]

/-- Every unitary trace test obeys the factor bound. -/
theorem nuclearTrace_unitary_factor_bound {n k : Type*}
    [Fintype n] [Fintype k] [DecidableEq n]
    (A B : Matrix n k ℂ) (U : Matrix n n ℂ) (hU : Uᴴ * U = 1) :
    ‖(Uᴴ * (A * Bᴴ)).trace‖ ≤ Real.sqrt (frobSq A * frobSq B) := by
  have ht : (Uᴴ * (A * Bᴴ)).trace = ((U * B)ᴴ * A).trace := by
    rw [Matrix.conjTranspose_mul]
    calc
      (Uᴴ * (A * Bᴴ)).trace = (Uᴴ * A * Bᴴ).trace := by rw [Matrix.mul_assoc]
      _ = (Bᴴ * (Uᴴ * A)).trace := Matrix.trace_mul_comm _ _
      _ = (Bᴴ * Uᴴ * A).trace := by rw [Matrix.mul_assoc]
  have h := nuclearTrace_pair_normSq_le (U * B) A
  rw [nuclearTrace_frobSq_isometry_mul U B hU, mul_comm, ← ht,
    Complex.normSq_eq_norm_sq] at h
  have hp : 0 ≤ frobSq A * frobSq B := mul_nonneg (frobSq_nonneg _) (frobSq_nonneg _)
  have hs := Real.sq_sqrt hp
  have hn := Real.sqrt_nonneg (frobSq A * frobSq B)
  have hz := norm_nonneg ((Uᴴ * (A * Bᴴ)).trace)
  nlinarith

/-- The actual unitary trace tests on a square complex matrix. -/
def nuclearTraceTests {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) : Set ℝ :=
  {r | ∃ U : Matrix n n ℂ, Uᴴ * U = 1 ∧ r = ‖(Uᴴ * X).trace‖}

/-- Nuclear trace norm, in its exact square-matrix variational form. -/
def nuclearTrace {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) : ℝ := sSup (nuclearTraceTests X)

theorem nuclearTraceTests_nonempty {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) : (nuclearTraceTests X).Nonempty := by
  refine ⟨‖X.trace‖, 1, ?_, ?_⟩ <;> simp

/-- All tests are bounded, including for empty index types. -/
theorem nuclearTraceTests_bddAbove {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) : BddAbove (nuclearTraceTests X) := by
  refine ⟨Real.sqrt (frobSq X * frobSq (1 : Matrix n n ℂ)), ?_⟩
  rintro r ⟨U, hU, rfl⟩
  simpa only [Matrix.conjTranspose_one, Matrix.mul_one] using
    nuclearTrace_unitary_factor_bound X (1 : Matrix n n ℂ) U hU

/-- Every genuine unitary test is at most the variational norm. -/
theorem nuclearTrace_test_le {n : Type*} [Fintype n] [DecidableEq n]
    (X U : Matrix n n ℂ) (hU : Uᴴ * U = 1) :
    ‖(Uᴴ * X).trace‖ ≤ nuclearTrace X :=
  le_csSup (nuclearTraceTests_bddAbove X) ⟨U, hU, rfl⟩

theorem nuclearTrace_nonneg {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) : 0 ≤ nuclearTrace X := by
  exact (norm_nonneg _).trans (nuclearTrace_test_le X 1 (by simp))

/-- The Schatten (1,2,2) factor bound, derived from the literal finite trace tests. -/
theorem nuclearTrace_mul_conjTranspose_le {n k : Type*}
    [Fintype n] [Fintype k] [DecidableEq n]
    (A B : Matrix n k ℂ) :
    nuclearTrace (A * Bᴴ) ≤ Real.sqrt (frobSq A * frobSq B) := by
  apply csSup_le (nuclearTraceTests_nonempty _)
  rintro r ⟨U, hU, rfl⟩
  exact nuclearTrace_unitary_factor_bound A B U hU

/-- The exact compound factor bound needed in the reduced-transition argument. -/
theorem nuclearTrace_compound_mul_conjTranspose_le {n k : Type*}
    [Fintype n] [Fintype k] [DecidableEq n]
    (A B : Matrix n k ℂ) :
    nuclearTrace (zeroReserveCompound (A * Bᴴ)) ≤
      Real.sqrt (frobSq (zeroReserveCompound A) * frobSq (zeroReserveCompound B)) := by
  rw [zeroReserveCompound_mul, zeroReserveCompound_conjTranspose]
  exact nuclearTrace_mul_conjTranspose_le _ _

end ThreeCopyQutritWerner
