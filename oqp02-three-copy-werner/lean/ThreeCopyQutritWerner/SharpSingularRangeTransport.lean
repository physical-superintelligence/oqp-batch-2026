module

public import ThreeCopyQutritWerner.SharpLocalCongruence
public import ThreeCopyQutritWerner.SharpPartialTraceMinors
public import ThreeCopyQutritWerner.SingularValueRank

@[expose] public section


/-!
# Singular physical reshapes under local congruence

The vector reshaping convention sends U tensor V to ordinary two-sided
multiplication U M V-transpose. Consequently every singular range vector
remains singular under arbitrary local congruence. The singular-range
hypothesis itself follows from actual sharp partial-trace saturation.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate Kronecker

namespace ThreeCopyQutritWerner

/-- The original reshape transforms by an ordinary transpose on the right. -/
theorem sharpReshape_kronecker_mulVec
    {L R : Type*} [Fintype L] [Fintype R]
    (U : Matrix L L ℂ) (V : Matrix R R ℂ) (v : L × R → ℂ) :
    sharpReshape ((U ⊗ₖ V) *ᵥ v) = U * sharpReshape v * Vᵀ := by
  ext i j
  simp only [sharpReshape, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Matrix.kroneckerMap_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- Actual local congruence preserves singularity of every range reshape;
unitarity is not needed for this forward implication. -/
theorem sharpSingularRange_local_congruence
    {n : Type*} [Fintype n] [DecidableEq n]
    (U V : Matrix n n ℂ) (Y : Matrix (n × n) (n × n) ℂ)
    (hrange : ∀ v : n × n → ℂ, (sharpReshape (Y *ᵥ v)).det = 0) :
    ∀ v : n × n → ℂ,
      (sharpReshape (((U ⊗ₖ V) * Y * (U ⊗ₖ V)ᵀ) *ᵥ v)).det = 0 := by
  intro v
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    sharpReshape_kronecker_mulVec, Matrix.det_mul, Matrix.det_mul, hrange]
  simp

/-- Sharp partial-trace saturation makes every original range reshape singular.
The coefficients are supplied by the actual singular reconstruction. -/
theorem sharpPartialTrace_range_reshape_det_zero
    (X : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ)
    (hsat : frobSq (ptraceL X) + frobSq (ptraceR X) =
      nuclearTrace X ^ 2 + Complex.normSq X.trace)
    (v : Fin 3 × Fin 3 → ℂ) : (sharpReshape (X *ᵥ v)).det = 0 := by
  classical
  let z : SingularPositiveIndex X → ℂ := fun k =>
    (singularWeight X k : ℂ) * ∑ j, conj (singularRight X k j) * v j
  have he : X *ᵥ v = fun r => ∑ k, z k * singularLeft X k r := by
    funext r
    simp only [Matrix.mulVec, dotProduct, singularFamily_reconstruct X,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    simp only [z, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  exact sharpPartialTrace_singular_common_reshape_det_zero X hsat z

/-- In particular the original range hypothesis needed by diagonal sharp
rigidity is retained in every actual local coordinate system. -/
theorem sharpPartialTrace_local_congruence_range_reshape_det_zero
    (X : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ)
    (hsat : frobSq (ptraceL X) + frobSq (ptraceR X) =
      nuclearTrace X ^ 2 + Complex.normSq X.trace)
    (U V : Matrix (Fin 3) (Fin 3) ℂ) :
    ∀ v : Fin 3 × Fin 3 → ℂ,
      (sharpReshape (((U ⊗ₖ V) * X * (U ⊗ₖ V)ᵀ) *ᵥ v)).det = 0 :=
  sharpSingularRange_local_congruence U V X
    (sharpPartialTrace_range_reshape_det_zero X hsat)

end ThreeCopyQutritWerner
