module

public import ThreeCopyQutritWerner.TraceEqualityScale
public import ThreeCopyQutritWerner.OrthogonalProjectionRange
public import ThreeCopyQutritWerner.ZeroFamilies

@[expose] public section


/-!
# The canonical projection of a saturated original trace block

The projection is literally 2C/Tr(C), including the original complex phase.
Its range is the original matrix range. The projection properties follow
from the proved equality classification, not from a supplied support plane.
-/

noncomputable section

open scoped Matrix ComplexConjugate

namespace ThreeCopyQutritWerner

/-- Nonzero scalar multiplication preserves the literal matrix column range. -/
theorem matrix_range_smul_eq {n m : Type*} [Fintype n] [Fintype m]
    (A : Matrix n m ℂ) (z : ℂ) (hz : z ≠ 0) :
    LinearMap.range (z • A).mulVecLin = LinearMap.range A.mulVecLin := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    refine ⟨z • v, ?_⟩
    change A *ᵥ (z • v) = (z • A) *ᵥ v
    rw [Matrix.mulVec_smul, Matrix.smul_mulVec]
  · rintro _ ⟨v, rfl⟩
    refine ⟨z⁻¹ • v, ?_⟩
    change (z • A) *ᵥ (z⁻¹ • v) = A *ᵥ v
    rw [Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul,
      mul_inv_cancel₀ hz, one_smul]

/-- The literal trace-normalized original matrix. -/
def traceNormalizedProjection {n : Type*} [Fintype n] (C : Matrix n n ℂ) :
    Matrix n n ℂ := (2 / C.trace) • C

/-- Exact restoration of the original scalar, without any positivity premise. -/
theorem traceNormalizedProjection_reconstruct {n : Type*} [Fintype n]
    (C : Matrix n n ℂ) (ht : C.trace ≠ 0) :
    C = (C.trace / 2) • traceNormalizedProjection C := by
  rw [traceNormalizedProjection, smul_smul]
  have h : C.trace / 2 * (2 / C.trace) = 1 := by field_simp
  rw [h, one_smul]

/-- Every nonzero trace-saturated rank-two block gives its actual Hermitian
idempotent of rank two, trace two, and exactly the original range. -/
theorem traceNormalizedProjection_properties
    {n : Type*} [Fintype n] [DecidableEq n]
    (C : Matrix n n ℂ) (hC : C.rank ≤ 2) (hne : C ≠ 0)
    (hT : Complex.normSq C.trace = 2 * frobSq C) :
    (traceNormalizedProjection C).IsHermitian ∧
      traceNormalizedProjection C * traceNormalizedProjection C = traceNormalizedProjection C ∧
      (traceNormalizedProjection C).rank = 2 ∧
      (traceNormalizedProjection C).trace = 2 ∧
      LinearMap.range (traceNormalizedProjection C).mulVecLin = LinearMap.range C.mulVecLin := by
  obtain ⟨e₀, e₁, h₀, h₁, h01, ht, he⟩ :=
    eq_trace_smul_proj_of_trace_bound_saturated C hC hne hT
  have hp : traceNormalizedProjection C = ketBra e₀ e₀ + ketBra e₁ e₁ := by
    change (2 / C.trace) • C = _
    calc
      _ = (2 / C.trace) • ((C.trace / 2) • (ketBra e₀ e₀ + ketBra e₁ e₁)) :=
        congrArg (fun D : Matrix n n ℂ => (2 / C.trace) • D) he
      _ = _ := by
        rw [smul_smul]
        have h : 2 / C.trace * (C.trace / 2) = 1 := by field_simp
        rw [h, one_smul]
  have h10 : braket e₁ e₀ = 0 := by
    rw [← conj_braket, h01, map_zero]
  have hc : (2 : ℂ) / C.trace ≠ 0 := div_ne_zero (by norm_num) ht
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change (traceNormalizedProjection C)ᴴ = traceNormalizedProjection C
    rw [hp, Matrix.conjTranspose_add, conjTranspose_ketBra, conjTranspose_ketBra]
  · rw [hp]
    simp only [Matrix.add_mul, Matrix.mul_add, ketBra_mul_ketBra, braket_self,
      h₀, h₁, h01, h10, Complex.ofReal_one, one_smul, zero_smul, zero_add, add_zero]
  · rw [traceNormalizedProjection,
      Matrix.rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero hc)]
    exact rank_two_of_trace_bound_saturated C hC hne hT
  · rw [hp, Matrix.trace_add, trace_ketBra, trace_ketBra, braket_self, braket_self,
      h₀, h₁, Complex.ofReal_one]
    norm_num
  · exact matrix_range_smul_eq C _ hc

end ThreeCopyQutritWerner
