module

public import VacuumBellSeparation.Gaussian.WhitenedComplexFamily

@[expose] public section


/-! # Actual real Hilbert product operators

The norm is the genuine L2 product norm. Componentwise skew operators
remain skew and retain a common operator-norm bound.
-/

noncomputable section

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

def realHilbertProductOperator (A : E →L[ℝ] E) (B : F →L[ℝ] F) :
    WithLp 2 (E × F) →L[ℝ] WithLp 2 (E × F) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ E F).symm.toContinuousLinearMap.comp
    ((A.prodMap B).comp (WithLp.prodContinuousLinearEquiv 2 ℝ E F).toContinuousLinearMap)

@[simp] theorem realHilbertProductOperator_apply (A : E →L[ℝ] E) (B : F →L[ℝ] F)
    (z : WithLp 2 (E × F)) :
    realHilbertProductOperator A B z = WithLp.toLp 2 (A z.fst, B z.snd) := rfl

theorem norm_realHilbertProductOperator_le (A : E →L[ℝ] E) (B : F →L[ℝ] F)
    {c : ℝ} (hc : 0 ≤ c) (hA : ‖A‖ ≤ c) (hB : ‖B‖ ≤ c) :
    ‖realHilbertProductOperator A B‖ ≤ c := by
  apply ContinuousLinearMap.opNorm_le_bound _ hc
  intro z
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg _))).mp
  rw [realHilbertProductOperator_apply, WithLp.prod_norm_sq_eq_of_L2, mul_pow,
    WithLp.prod_norm_sq_eq_of_L2]
  change ‖A z.fst‖ ^ 2 + ‖B z.snd‖ ^ 2 ≤ c ^ 2 * (‖z.fst‖ ^ 2 + ‖z.snd‖ ^ 2)
  have ha := (A.le_opNorm z.fst).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
  have hb := (B.le_opNorm z.snd).trans (mul_le_mul_of_nonneg_right hB (norm_nonneg _))
  calc
    _ ≤ (c * ‖z.fst‖) ^ 2 + (c * ‖z.snd‖) ^ 2 := by gcongr
    _ = _ := by ring

theorem realHilbertProductOperator_mem_skewAdjoint
    {A : E →L[ℝ] E} {B : F →L[ℝ] F}
    (hA : A ∈ skewAdjoint (E →L[ℝ] E)) (hB : B ∈ skewAdjoint (F →L[ℝ] F)) :
    realHilbertProductOperator A B ∈ skewAdjoint
      (WithLp 2 (E × F) →L[ℝ] WithLp 2 (E × F)) := by
  change (realHilbertProductOperator A B).adjoint = -realHilbertProductOperator A B
  change A.adjoint = -A at hA
  change B.adjoint = -B at hB
  ext y
  apply ext_inner_left ℝ
  intro x
  rw [adjoint_inner_right, neg_apply, inner_neg_right]
  simp only [realHilbertProductOperator_apply, WithLp.prod_inner_apply,
    WithLp.ofLp_toLp, Prod.fst, Prod.snd]
  rw [← A.adjoint_inner_right, ← B.adjoint_inner_right, hA, hB,
    neg_apply, neg_apply, inner_neg_right, inner_neg_right]
  simp only [WithLp.ofLp_fst, WithLp.ofLp_snd] <;> ring

end VacuumBellSeparation.Gaussian
