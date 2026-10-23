module

public import ThreeCopyQutritWerner.CertificateBlockPositivity
public import ThreeCopyQutritWerner.Embedding

@[expose] public section


/-!
# Physical trace metrics from a bijective intertwiner

An exact full basis transports traces of operator products by similarity.
For Hermitian physical operators this recovers the Hilbert--Schmidt metric,
even though the generating basis itself need not be orthogonal. Repeated
source-frame blocks therefore give their literal representation multiplicities.
-/

noncomputable section

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

/-- A bijective rectangular coordinate map has an actual two-sided inverse. -/
theorem certificate_exists_inverse_of_bijective
    {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (S : Matrix n m ℂ) (hS : Function.Bijective S.mulVec) :
    ∃ T : Matrix m n ℂ, S * T = 1 ∧ T * S = 1 := by
  obtain ⟨T, hT⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp hS.2
  refine ⟨T, hT, ?_⟩
  apply Matrix.mulVec_injective
  funext v
  apply hS.1
  simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hT, Matrix.one_mul,
    Matrix.mul_one]

/-- Exact intertwining through a full basis preserves the trace. -/
theorem certificate_trace_of_bijective_intertwiner
    {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (M : Matrix n n ℂ) (S : Matrix n m ℂ) (A : Matrix m m ℂ)
    (hS : Function.Bijective S.mulVec) (hinter : M * S = S * A) :
    M.trace = A.trace := by
  obtain ⟨T, hST, hTS⟩ := certificate_exists_inverse_of_bijective S hS
  have hrepr : M = S * A * T := by
    rw [← hinter, Matrix.mul_assoc, hST, Matrix.mul_one]
  rw [hrepr, Matrix.trace_mul_cycle, hTS, Matrix.one_mul]

/-- The same basis transports the trace pairing of two physical operators. -/
theorem certificate_trace_mul_of_bijective_intertwiner
    {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (M N : Matrix n n ℂ) (S : Matrix n m ℂ) (A B : Matrix m m ℂ)
    (hS : Function.Bijective S.mulVec)
    (hM : M * S = S * A) (hN : N * S = S * B) :
    (M * N).trace = (A * B).trace := by
  apply certificate_trace_of_bijective_intertwiner (M * N) S (A * B) hS
  rw [Matrix.mul_assoc, hN, ← Matrix.mul_assoc, hM, Matrix.mul_assoc]

/-- Hermitian physical Frobenius norm is recovered from the coefficient operator,
which is not assumed Hermitian in the Euclidean coordinate metric. -/
theorem certificate_frobSq_of_bijective_intertwiner
    {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (M : Matrix n n ℂ) (S : Matrix n m ℂ) (A : Matrix m m ℂ)
    (hM : M.IsHermitian) (hS : Function.Bijective S.mulVec)
    (hinter : M * S = S * A) :
    (frobSq M : ℂ) = (A * A).trace := by
  rw [ofReal_frobSq_eq_trace, hM.eq]
  exact certificate_trace_mul_of_bijective_intertwiner M M S A A hS hinter hinter

/-- Repeated frame blocks contribute once per actual occurrence in the full basis. -/
theorem certificate_trace_mul_blocks
    {ι : Type*} {m : ι → Type*} [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (m i)]
    (A B : ∀ i, Matrix (m i) (m i) ℂ) :
    (Matrix.blockDiagonal' A * Matrix.blockDiagonal' B).trace =
      ∑ i, (A i * B i).trace := by
  rw [← Matrix.blockDiagonal'_mul, Matrix.trace_blockDiagonal']

end ThreeCopyQutritWerner
