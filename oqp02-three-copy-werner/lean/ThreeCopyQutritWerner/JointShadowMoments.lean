module

public import ThreeCopyQutritWerner.JointShadowPhysical
public import ThreeCopyQutritWerner.JointShadowExpansion

@[expose] public section


/-! All sixteen common replica moments in the actual physical coordinates. -/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace ThreeCopyQutritWerner

/-- The complementary grouped swap contracts the opposite partial trace. -/
theorem jointShadowSwapForm_complement
    {n u v : Type*} [Fintype n] [Fintype u] [Fintype v]
    (e : n ≃ u × v) (x y : n → ℂ) :
    jointShadowSwapForm (e.trans (Equiv.prodComm u v)) x y =
      (frobSq (ptraceR (ketBra (x ∘ e.symm) (y ∘ e.symm))) : ℂ) := by
  rw [jointShadowSwapForm_eq_partialTrace]
  congr 2

variable {l a b c : Type*} [Fintype l] [Fintype a] [Fintype b] [Fintype c]

/-- The two-replica vector consists of the same two literal purifications. -/
def jointShadowSourceTensor (X Y : Matrix (a × b × c) l ℂ) :=
  jointShadowTensor (jointShadowPurification X) (jointShadowPurification Y)

/-- Swapping precisely physical subsystem A gives its original reduced-density overlap. -/
theorem jointShadowMoment_A (X Y : Matrix (a × b × c) l ℂ) :
    jointShadowMoment (jointShadowSourceTensor X Y) false true false false =
      (hsInner (ptrace₂₃ (X * Xᴴ)) (ptrace₂₃ (Y * Yᴴ))).re := by
  change (jointShadowSwapForm jointShadowSplitA
    (jointShadowPurification X) (jointShadowPurification Y)).re = _
  rw [jointShadowSwapForm_eq_reduced_overlap]
  change (hsInner (jointShadowReduced jointShadowSplitA X X)
    (jointShadowReduced jointShadowSplitA Y Y)).re = _
  rw [jointShadowReduced_A, jointShadowReduced_A]

/-- The complementary swap, including L, is the actual A transition marginal norm. -/
theorem jointShadowMoment_LBC (X Y : Matrix (a × b × c) l ℂ) :
    jointShadowMoment (jointShadowSourceTensor X Y) true false true true =
      frobSq (ptrace₂₃ (X * Yᴴ)) := by
  change (jointShadowSwapForm (jointShadowSplitA.trans (Equiv.prodComm _ _))
    (jointShadowPurification X) (jointShadowPurification Y)).re = _
  rw [jointShadowSwapForm_complement, Complex.ofReal_re]
  change frobSq (jointShadowReduced jointShadowSplitA X Y) = _
  rw [jointShadowReduced_A]

/-- Swapping precisely physical subsystem B gives its original reduced-density overlap. -/
theorem jointShadowMoment_B (X Y : Matrix (a × b × c) l ℂ) :
    jointShadowMoment (jointShadowSourceTensor X Y) false false true false =
      (hsInner (ptrace₁₃ (X * Xᴴ)) (ptrace₁₃ (Y * Yᴴ))).re := by
  change (jointShadowSwapForm jointShadowSplitB
    (jointShadowPurification X) (jointShadowPurification Y)).re = _
  rw [jointShadowSwapForm_eq_reduced_overlap]
  change (hsInner (jointShadowReduced jointShadowSplitB X X)
    (jointShadowReduced jointShadowSplitB Y Y)).re = _
  rw [jointShadowReduced_B, jointShadowReduced_B]

/-- The complementary swap, including L, is the actual B transition marginal norm. -/
theorem jointShadowMoment_LAC (X Y : Matrix (a × b × c) l ℂ) :
    jointShadowMoment (jointShadowSourceTensor X Y) true true false true =
      frobSq (ptrace₁₃ (X * Yᴴ)) := by
  change (jointShadowSwapForm (jointShadowSplitB.trans (Equiv.prodComm _ _))
    (jointShadowPurification X) (jointShadowPurification Y)).re = _
  rw [jointShadowSwapForm_complement, Complex.ofReal_re]
  change frobSq (jointShadowReduced jointShadowSplitB X Y) = _
  rw [jointShadowReduced_B]

/-- Swapping precisely physical subsystem C gives its original reduced-density overlap. -/
theorem jointShadowMoment_C (X Y : Matrix (a × b × c) l ℂ) :
    jointShadowMoment (jointShadowSourceTensor X Y) false false false true =
      (hsInner (ptrace₁₂ (X * Xᴴ)) (ptrace₁₂ (Y * Yᴴ))).re := by
  change (jointShadowSwapForm jointShadowSplitC
    (jointShadowPurification X) (jointShadowPurification Y)).re = _
  rw [jointShadowSwapForm_eq_reduced_overlap]
  change (hsInner (jointShadowReduced jointShadowSplitC X X)
    (jointShadowReduced jointShadowSplitC Y Y)).re = _
  rw [jointShadowReduced_C, jointShadowReduced_C]

/-- The complementary swap, including L, is the actual C transition marginal norm. -/
theorem jointShadowMoment_LAB (X Y : Matrix (a × b × c) l ℂ) :
    jointShadowMoment (jointShadowSourceTensor X Y) true true true false =
      frobSq (ptrace₁₂ (X * Yᴴ)) := by
  change (jointShadowSwapForm (jointShadowSplitC.trans (Equiv.prodComm _ _))
    (jointShadowPurification X) (jointShadowPurification Y)).re = _
  rw [jointShadowSwapForm_complement, Complex.ofReal_re]
  change frobSq (jointShadowReduced jointShadowSplitC X Y) = _
  rw [jointShadowReduced_C]

/-- Swapping precisely physical subsystem AB gives its original reduced-density overlap. -/
theorem jointShadowMoment_AB (X Y : Matrix (a × b × c) l ℂ) :
    jointShadowMoment (jointShadowSourceTensor X Y) false true true false =
      (hsInner (ptrace₃ (X * Xᴴ)) (ptrace₃ (Y * Yᴴ))).re := by
  change (jointShadowSwapForm jointShadowSplitAB
    (jointShadowPurification X) (jointShadowPurification Y)).re = _
  rw [jointShadowSwapForm_eq_reduced_overlap]
  change (hsInner (jointShadowReduced jointShadowSplitAB X X)
    (jointShadowReduced jointShadowSplitAB Y Y)).re = _
  rw [jointShadowReduced_AB, jointShadowReduced_AB]

/-- The complementary swap, including L, is the actual AB transition marginal norm. -/
theorem jointShadowMoment_LC (X Y : Matrix (a × b × c) l ℂ) :
    jointShadowMoment (jointShadowSourceTensor X Y) true false false true =
      frobSq (ptrace₃ (X * Yᴴ)) := by
  change (jointShadowSwapForm (jointShadowSplitAB.trans (Equiv.prodComm _ _))
    (jointShadowPurification X) (jointShadowPurification Y)).re = _
  rw [jointShadowSwapForm_complement, Complex.ofReal_re]
  change frobSq (jointShadowReduced jointShadowSplitAB X Y) = _
  rw [jointShadowReduced_AB]

/-- Swapping precisely physical subsystem AC gives its original reduced-density overlap. -/
theorem jointShadowMoment_AC (X Y : Matrix (a × b × c) l ℂ) :
    jointShadowMoment (jointShadowSourceTensor X Y) false true false true =
      (hsInner (ptrace₂ (X * Xᴴ)) (ptrace₂ (Y * Yᴴ))).re := by
  change (jointShadowSwapForm jointShadowSplitAC
    (jointShadowPurification X) (jointShadowPurification Y)).re = _
  rw [jointShadowSwapForm_eq_reduced_overlap]
  change (hsInner (jointShadowReduced jointShadowSplitAC X X)
    (jointShadowReduced jointShadowSplitAC Y Y)).re = _
  rw [jointShadowReduced_AC, jointShadowReduced_AC]

/-- The complementary swap, including L, is the actual AC transition marginal norm. -/
theorem jointShadowMoment_LB (X Y : Matrix (a × b × c) l ℂ) :
    jointShadowMoment (jointShadowSourceTensor X Y) true false true false =
      frobSq (ptrace₂ (X * Yᴴ)) := by
  change (jointShadowSwapForm (jointShadowSplitAC.trans (Equiv.prodComm _ _))
    (jointShadowPurification X) (jointShadowPurification Y)).re = _
  rw [jointShadowSwapForm_complement, Complex.ofReal_re]
  change frobSq (jointShadowReduced jointShadowSplitAC X Y) = _
  rw [jointShadowReduced_AC]

/-- Swapping precisely physical subsystem BC gives its original reduced-density overlap. -/
theorem jointShadowMoment_BC (X Y : Matrix (a × b × c) l ℂ) :
    jointShadowMoment (jointShadowSourceTensor X Y) false false true true =
      (hsInner (ptrace₁ (X * Xᴴ)) (ptrace₁ (Y * Yᴴ))).re := by
  change (jointShadowSwapForm jointShadowSplitBC
    (jointShadowPurification X) (jointShadowPurification Y)).re = _
  rw [jointShadowSwapForm_eq_reduced_overlap]
  change (hsInner (jointShadowReduced jointShadowSplitBC X X)
    (jointShadowReduced jointShadowSplitBC Y Y)).re = _
  rw [jointShadowReduced_BC, jointShadowReduced_BC]

/-- The complementary swap, including L, is the actual BC transition marginal norm. -/
theorem jointShadowMoment_LA (X Y : Matrix (a × b × c) l ℂ) :
    jointShadowMoment (jointShadowSourceTensor X Y) true true false false =
      frobSq (ptrace₁ (X * Yᴴ)) := by
  change (jointShadowSwapForm (jointShadowSplitBC.trans (Equiv.prodComm _ _))
    (jointShadowPurification X) (jointShadowPurification Y)).re = _
  rw [jointShadowSwapForm_complement, Complex.ofReal_re]
  change frobSq (jointShadowReduced jointShadowSplitBC X Y) = _
  rw [jointShadowReduced_BC]

/-- Swapping precisely physical subsystem ABC gives its original reduced-density overlap. -/
theorem jointShadowMoment_ABC (X Y : Matrix (a × b × c) l ℂ) :
    jointShadowMoment (jointShadowSourceTensor X Y) false true true true =
      (hsInner ((X * Xᴴ)) ((Y * Yᴴ))).re := by
  change (jointShadowSwapForm jointShadowSplitABC
    (jointShadowPurification X) (jointShadowPurification Y)).re = _
  rw [jointShadowSwapForm_eq_reduced_overlap]
  change (hsInner (jointShadowReduced jointShadowSplitABC X X)
    (jointShadowReduced jointShadowSplitABC Y Y)).re = _
  rw [jointShadowReduced_ABC, jointShadowReduced_ABC]

/-- The complementary swap, including L, is the actual ABC transition marginal norm. -/
theorem jointShadowMoment_L (X Y : Matrix (a × b × c) l ℂ) :
    jointShadowMoment (jointShadowSourceTensor X Y) true false false false =
      frobSq ((X * Yᴴ)) := by
  change (jointShadowSwapForm (jointShadowSplitABC.trans (Equiv.prodComm _ _))
    (jointShadowPurification X) (jointShadowPurification Y)).re = _
  rw [jointShadowSwapForm_complement, Complex.ofReal_re]
  change frobSq (jointShadowReduced jointShadowSplitABC X Y) = _
  rw [jointShadowReduced_ABC]

/-- No local swaps give the product of the two actual purification norms. -/
theorem jointShadowMoment_empty (X Y : Matrix (a × b × c) l ℂ) :
    jointShadowMoment (jointShadowSourceTensor X Y) false false false false =
      vecNormSq (jointShadowPurification X) * vecNormSq (jointShadowPurification Y) := by
  have h := congrArg Complex.re (sum_conj_tensor_self
    (jointShadowPurification X) (jointShadowPurification Y))
  simpa only [jointShadowMoment, jointShadowSourceTensor, jointShadowTensor,
    braket, Bool.false_eq_true, ite_false, Equiv.refl_apply, Complex.ofReal_re] using h

/-- Full replica exchange gives the exact purification overlap square. -/
theorem jointShadowMoment_full (X Y : Matrix (a × b × c) l ℂ) :
    jointShadowMoment (jointShadowSourceTensor X Y) true true true true =
      Complex.normSq (braket (jointShadowPurification Y) (jointShadowPurification X)) := by
  have h := congrArg Complex.re (sum_conj_tensor_swap
    (jointShadowPurification X) (jointShadowPurification Y))
  simpa only [jointShadowMoment, jointShadowSourceTensor, jointShadowTensor,
    braket, if_true, jointShadowSwapL, jointShadowSwapA, jointShadowSwapB,
    jointShadowSwapC, Equiv.coe_fn_mk, Complex.ofReal_re] using h

/-- Full replica overlap is exactly the existing trace invariant of XY†. -/
theorem jointShadowSource_trace (X Y : Matrix (a × b × c) l ℂ) :
    braket (jointShadowPurification Y) (jointShadowPurification X) = (X * Yᴴ).trace := by
  simp only [braket, jointShadowPurification, Fintype.sum_prod_type,
    Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.star_def]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro r _
  ring

/-- The purification norm agrees with the original rectangular Frobenius norm. -/
theorem jointShadowSource_norm (X : Matrix (a × b × c) l ℂ) :
    vecNormSq (jointShadowPurification X) = frobSq X := by
  simp only [vecNormSq, jointShadowPurification, frobSq, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]

end ThreeCopyQutritWerner
