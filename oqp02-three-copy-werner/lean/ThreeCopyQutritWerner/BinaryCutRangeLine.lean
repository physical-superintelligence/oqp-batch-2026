module

public import ThreeCopyQutritWerner.SkewRangeLine
public import ThreeCopyQutritWerner.BinaryCutKernel

@[expose] public section


/-!
# Fixed-source uniqueness in the trace-zero binary cut kernel

The spin transform is ordinary-transpose skew and preserves the actual
range. A rank-two anchor therefore fixes the entire trace-zero cut-kernel
line on that source. Nonzero-trace identity-factor branches remain separate.
-/

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

/-- Rank and norm assumptions are unnecessary for the trace-zero spin identity. -/
theorem binaryCut_trace_zero_spin_skew
    (C : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (hq : cutForm C = 0) (ht : C.trace = 0) :
    (C * epsJ₂)ᵀ = -(C * epsJ₂) := by
  obtain ⟨A, B, hA, hB, he⟩ := binaryCut_zero_kronecker_decomposition C hq
  rw [ht, zero_div] at he
  rw [he]
  exact binaryKroneckerSum_zero_scalar_spin A B hA hB

/-- A second trace-zero binary cut zero supported on the actual rank-two
source of an anchor is a scalar multiple of that anchor. -/
theorem binaryCut_trace_zero_eq_smul_of_range_le
    (A B : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (hA : cutForm A = 0) (hB : cutForm B = 0)
    (htA : A.trace = 0) (htB : B.trace = 0) (hr : A.rank = 2)
    (hBA : LinearMap.range B.mulVecLin ≤ LinearMap.range A.mulVecLin) :
    ∃ z : ℂ, B = z • A := by
  have hJ : epsJ₂ * epsJ₂ᵀ = 1 :=
    (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl (Fin 2 × Fin 2))).mp
      epsJ₂_transpose_mul_self
  have hrank (X : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
      (X * epsJ₂).rank = X.rank := by
    apply le_antisymm (Matrix.rank_mul_le_left _ _)
    calc
      X.rank = (X * epsJ₂ * epsJ₂ᵀ).rank := by rw [Matrix.mul_assoc, hJ, Matrix.mul_one]
      _ ≤ (X * epsJ₂).rank := Matrix.rank_mul_le_left _ _
  have hrange (X : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
      LinearMap.range (X * epsJ₂).mulVecLin = LinearMap.range X.mulVecLin :=
    matrix_range_mul_eq_of_rank_eq X epsJ₂ (hrank X)
  have hrBA : LinearMap.range (B * epsJ₂).mulVecLin ≤
      LinearMap.range (A * epsJ₂).mulVecLin := by
    simpa only [hrange] using hBA
  obtain ⟨z, hz⟩ := skew_eq_smul_of_range_le_rank_two (A * epsJ₂) (B * epsJ₂)
    (binaryCut_trace_zero_spin_skew A hA htA) (binaryCut_trace_zero_spin_skew B hB htB)
    ((hrank A).trans hr) hrBA
  refine ⟨z, ?_⟩
  have he := congrArg (fun M => M * epsJ₂ᵀ) hz
  simpa only [Matrix.smul_mul, Matrix.mul_assoc, hJ, Matrix.mul_one] using he

end ThreeCopyQutritWerner
