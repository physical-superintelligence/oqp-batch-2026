module

public import VacuumBellSeparation.Gaussian.SourceMapConstruction
public import VacuumBellSeparation.Gaussian.ComplexifiedOperator
public import VacuumBellSeparation.FreeField.RealCommutation

@[expose] public section


/-!
# The actual complex source map and its Gram operator

A real isometry `K` into the physical complex one-particle space extends to
`κ(x+iy)=Kx+iKy`. This map is bounded by `sqrt 2`; it is not assumed to be
isometric or injective. Its actual Gram operator is `1+(i/2) J_C`, where
`J_C` is the componentwise extension of the constructed real commutation
operator. This supplies the physical origin of the normalized Gram formula.
-/

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap HilbertComplexification
open scoped ComplexConjugate

variable {E H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

@[simp]
theorem sourceMap_apply (K : E →ₗᵢ[ℝ] H) (z : HilbertComplexification E) :
    sourceMap K z = K z.re + Complex.I • K z.im := rfl

theorem norm_sourceMap_le_sqrt_two (K : E →ₗᵢ[ℝ] H) : ‖sourceMap K‖ ≤ Real.sqrt 2 :=
  ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) (norm_sourceMapLinear_le K)

@[simp]
theorem sourceMap_ofReal (K : E →ₗᵢ[ℝ] H) (x : E) : sourceMap K (ofReal x) = K x := by
  simp

theorem complexCommutation_mem_skewAdjoint (K : E →ₗᵢ[ℝ] H) :
    complexCommutation K ∈ skewAdjoint
      (HilbertComplexification E →L[ℂ] HilbertComplexification E) :=
  complexify_mem_skewAdjoint (realCommutation_mem_skewAdjoint K)

theorem norm_complexCommutation_le_two (K : E →ₗᵢ[ℝ] H) :
    ‖complexCommutation K‖ ≤ 2 := by
  rw [complexCommutation, norm_complexify]
  exact norm_realCommutation_le_two K

theorem inner_sourceMap_gram (K : E →ₗᵢ[ℝ] H) (z w : HilbertComplexification E) :
    inner ℂ (sourceMap K z) (sourceMap K w) =
      inner ℂ z ((1 + (Complex.I / 2) • complexCommutation K) w) := by
  simp only [sourceMap_apply, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, inner_realEmbedding_gram,
    add_apply, one_apply_eq_self, smul_apply, complexCommutation,
    HilbertComplexification.inner_eq, complexify_re, complexify_im]
  apply Complex.ext <;>
    simp [Complex.mul_re, Complex.mul_im] <;> ring

/-- The actual physical Gram operator, with the source's normalization and sign. -/
theorem sourceMap_adjoint_mul_self (K : E →ₗᵢ[ℝ] H) :
    (sourceMap K).adjoint.comp (sourceMap K) = 1 + (Complex.I / 2) • complexCommutation K := by
  apply ContinuousLinearMap.ext
  intro w
  apply ext_inner_left ℂ
  intro z
  change inner ℂ z ((sourceMap K).adjoint (sourceMap K w)) = _
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact inner_sourceMap_gram K z w

/-- Real source inclusions intertwine the actual complex physical maps. -/
theorem sourceMap_comp_complexifyIsometry
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (K : E →ₗᵢ[ℝ] H) (i : F →ₗᵢ[ℝ] E) :
    (sourceMap K).comp (complexifyIsometry i).toContinuousLinearMap = sourceMap (K.comp i) := by
  apply ContinuousLinearMap.ext
  intro z
  simp

end VacuumBellSeparation.Gaussian
