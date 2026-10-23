module

public import ThreeCopyQutritWerner.JointShadowProjection
public import ThreeCopyQutritWerner.ZeroReserveAlgebra

@[expose] public section


/-!
# Faithful swap contractions on arbitrary bipartitions

A coordinate equivalence only groups the original registers. The expectation
of the selected replica swap is the literal squared partial-trace norm, and
also the overlap of the complementary reduced pure-source density matrices.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace ThreeCopyQutritWerner

/-- Two original purification vectors in their two replica coordinates. -/
def jointShadowTensor {n : Type*} (x y : n → ℂ) : n × n → ℂ :=
  fun p => x p.1 * y p.2

/-- Exchange the first grouped subsystem after an actual coordinate equivalence. -/
def jointShadowSplitSwap {n u v : Type*} (e : n ≃ u × v) : n × n ≃ n × n where
  toFun p := (e.symm ((e p.2).1, (e p.1).2), e.symm ((e p.1).1, (e p.2).2))
  invFun p := (e.symm ((e p.2).1, (e p.1).2), e.symm ((e p.1).1, (e p.2).2))
  left_inv p := by simp
  right_inv p := by simp

/-- The literal grouped replica-swap expectation. -/
def jointShadowSwapForm {n u v : Type*} [Fintype n]
    (e : n ≃ u × v) (x y : n → ℂ) : ℂ :=
  braket (fun p => jointShadowTensor x y (jointShadowSplitSwap e p)) (jointShadowTensor x y)

/-- Exact contraction after grouping, with no normalization or rank assumption. -/
theorem jointShadowSwapForm_eq_partialTrace
    {n u v : Type*} [Fintype n] [Fintype u] [Fintype v]
    (e : n ≃ u × v) (x y : n → ℂ) :
    jointShadowSwapForm e x y =
      (frobSq (ptraceL (ketBra (x ∘ e.symm) (y ∘ e.symm))) : ℂ) := by
  rw [← sum_conj_tensor_swapLeft (x ∘ e.symm) (y ∘ e.symm)]
  unfold jointShadowSwapForm braket jointShadowTensor jointShadowSplitSwap
  apply Fintype.sum_equiv (Equiv.prodCongr e e)
  intro p
  simp only [Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd,
    Equiv.coe_fn_mk, Function.comp_apply, Equiv.symm_apply_apply]

/-- The same swap expectation is the actual reduced-density overlap on the
swapped subsystem. The order of the two densities is immaterial in the real part. -/
theorem jointShadowSwapForm_eq_reduced_overlap
    {n u v : Type*} [Fintype n] [Fintype u] [Fintype v]
    (e : n ≃ u × v) (x y : n → ℂ) :
    (jointShadowSwapForm e x y).re =
      (hsInner (ptraceR (ketBra (x ∘ e.symm) (x ∘ e.symm)))
        (ptraceR (ketBra (y ∘ e.symm) (y ∘ e.symm)))).re := by
  rw [jointShadowSwapForm_eq_partialTrace, Complex.ofReal_re,
    ← zeroReserve_hsInner_self_re, hsInner_ptraceL_ketBra_cross,
    hsInner_re_comm]

end ThreeCopyQutritWerner
