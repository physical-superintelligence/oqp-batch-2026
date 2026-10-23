module

public import ThreeCopyQutritWerner.JointShadowContractions

@[expose] public section


/-! Exact sixteen-term expansion of the common four-register shadow. -/

noncomputable section

open scoped BigOperators ComplexConjugate

namespace ThreeCopyQutritWerner

variable {l a b c : Type*} [Fintype l] [Fintype a] [Fintype b] [Fintype c]

/-- A literal simultaneous local-swap contraction of the original replica vector. -/
def jointShadowMoment
    (f : ((l × a × b × c) × (l × a × b × c)) → ℂ)
    (L A B C : Bool) : ℝ :=
  (braket (fun p => f
    ((if L then jointShadowSwapL else Equiv.refl _) 
      ((if A then jointShadowSwapA else Equiv.refl _)
        ((if B then jointShadowSwapB else Equiv.refl _)
          ((if C then jointShadowSwapC else Equiv.refl _) p))))) f).re

/-- Every term uses the same two replicas; the logical parity is positive
and each physical parity is negative. -/
theorem jointShadowProjection_sixteen_terms
    (f : ((l × a × b × c) × (l × a × b × c)) → ℂ) :
    16 * vecNormSq (jointShadowProjection f) =
      jointShadowMoment f false false false false
        + jointShadowMoment f true false false false
        - jointShadowMoment f false false false true
        - jointShadowMoment f true false false true
        - jointShadowMoment f false false true false
        - jointShadowMoment f true false true false
        + jointShadowMoment f false false true true
        + jointShadowMoment f true false true true
        - jointShadowMoment f false true false false
        - jointShadowMoment f true true false false
        + jointShadowMoment f false true false true
        + jointShadowMoment f true true false true
        + jointShadowMoment f false true true false
        + jointShadowMoment f true true true false
        - jointShadowMoment f false true true true
        - jointShadowMoment f true true true true
 := by
  have h : braket (jointShadowProjection f) f =
      (vecNormSq (jointShadowProjection f) : ℂ) := by
    rw [jointShadowProjection_selfadjoint]
    have hi := jointShadowProjection_selfadjoint f (jointShadowProjection f)
    rw [jointShadowProjection_idempotent, braket_self] at hi
    exact hi.symm
  rw [← Complex.ofReal_re (vecNormSq (jointShadowProjection f)), ← h]
  simp only [jointShadowMoment, braket, Complex.re_sum, Finset.mul_sum]
  simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p _
  rw [← Complex.re_ofReal_mul]
  simp only [← Complex.add_re, ← Complex.sub_re]
  apply congrArg Complex.re
  simp only [jointShadowProjection, jointShadowParity, Bool.false_eq_true,
    ite_false, ite_true, Equiv.refl_apply, jointShadowSwapL, jointShadowSwapA,
    jointShadowSwapB, jointShadowSwapC, Equiv.coe_fn_mk,
    Complex.ofReal_one, Complex.ofReal_neg, Complex.ofReal_ofNat,
    map_div₀, map_add, map_mul, map_neg, map_one, map_ofNat]
  ring

end ThreeCopyQutritWerner
