module

public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Module.Submodule.EqLocus
public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Data.Fintype.Order
public import Mathlib.Data.List.Enum
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.Tactic.Basify.Attr

@[expose] public section


/-!
Complete literal enumerations of S4 and S5. Row bijectivity and enumeration
injectivity are ordinary finite kernel checks; factorial cardinality supplies
surjectivity. Character sums still range over the entire symmetric groups.
-/

noncomputable section

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

open scoped BigOperators

namespace ThreeCopyQutritWerner

def certificatePerm4Images : Fin 24 → Fin 4 → Fin 4 :=
  ![![0, 1, 2, 3],
    ![0, 1, 3, 2],
    ![0, 2, 1, 3],
    ![0, 2, 3, 1],
    ![0, 3, 1, 2],
    ![0, 3, 2, 1],
    ![1, 0, 2, 3],
    ![1, 0, 3, 2],
    ![1, 2, 0, 3],
    ![1, 2, 3, 0],
    ![1, 3, 0, 2],
    ![1, 3, 2, 0],
    ![2, 0, 1, 3],
    ![2, 0, 3, 1],
    ![2, 1, 0, 3],
    ![2, 1, 3, 0],
    ![2, 3, 0, 1],
    ![2, 3, 1, 0],
    ![3, 0, 1, 2],
    ![3, 0, 2, 1],
    ![3, 1, 0, 2],
    ![3, 1, 2, 0],
    ![3, 2, 0, 1],
    ![3, 2, 1, 0]]

theorem certificatePerm4Images_bijective (i : Fin 24) :
    Function.Bijective (certificatePerm4Images i) := by
  fin_cases i <;> decide

def certificatePerm4InverseImages : Fin 24 → Fin 4 → Fin 4 :=
  ![![0, 1, 2, 3],
    ![0, 1, 3, 2],
    ![0, 2, 1, 3],
    ![0, 3, 1, 2],
    ![0, 2, 3, 1],
    ![0, 3, 2, 1],
    ![1, 0, 2, 3],
    ![1, 0, 3, 2],
    ![2, 0, 1, 3],
    ![3, 0, 1, 2],
    ![2, 0, 3, 1],
    ![3, 0, 2, 1],
    ![1, 2, 0, 3],
    ![1, 3, 0, 2],
    ![2, 1, 0, 3],
    ![3, 1, 0, 2],
    ![2, 3, 0, 1],
    ![3, 2, 0, 1],
    ![1, 2, 3, 0],
    ![1, 3, 2, 0],
    ![2, 1, 3, 0],
    ![3, 1, 2, 0],
    ![2, 3, 1, 0],
    ![3, 2, 1, 0]]

def certificatePerm4 (i : Fin 24) : Equiv.Perm (Fin 4) where
  toFun := certificatePerm4Images i
  invFun := certificatePerm4InverseImages i
  left_inv := by fin_cases i <;> decide
  right_inv := by fin_cases i <;> decide

theorem certificatePerm4_apply (i : Fin 24) (j : Fin 4) :
    certificatePerm4 i j = certificatePerm4Images i j := rfl

theorem certificatePerm4_bijective : Function.Bijective certificatePerm4 := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · intro i j h
    have hi : Function.Injective certificatePerm4Images := by decide
    apply hi
    funext k
    exact Equiv.congr_fun h k
  · norm_num [Fintype.card_perm, Nat.factorial]

theorem certificate_sum_perm4 {M : Type*} [AddCommMonoid M]
    (f : Equiv.Perm (Fin 4) → M) :
    (∑ σ, f σ) = ∑ i : Fin 24, f (certificatePerm4 i) := by
  symm
  exact Fintype.sum_equiv (Equiv.ofBijective certificatePerm4
    certificatePerm4_bijective) _ _ (fun _ => rfl)

def certificatePerm5Images : Fin 120 → Fin 5 → Fin 5 :=
  ![![0, 1, 2, 3, 4],
    ![0, 1, 2, 4, 3],
    ![0, 1, 3, 2, 4],
    ![0, 1, 3, 4, 2],
    ![0, 1, 4, 2, 3],
    ![0, 1, 4, 3, 2],
    ![0, 2, 1, 3, 4],
    ![0, 2, 1, 4, 3],
    ![0, 2, 3, 1, 4],
    ![0, 2, 3, 4, 1],
    ![0, 2, 4, 1, 3],
    ![0, 2, 4, 3, 1],
    ![0, 3, 1, 2, 4],
    ![0, 3, 1, 4, 2],
    ![0, 3, 2, 1, 4],
    ![0, 3, 2, 4, 1],
    ![0, 3, 4, 1, 2],
    ![0, 3, 4, 2, 1],
    ![0, 4, 1, 2, 3],
    ![0, 4, 1, 3, 2],
    ![0, 4, 2, 1, 3],
    ![0, 4, 2, 3, 1],
    ![0, 4, 3, 1, 2],
    ![0, 4, 3, 2, 1],
    ![1, 0, 2, 3, 4],
    ![1, 0, 2, 4, 3],
    ![1, 0, 3, 2, 4],
    ![1, 0, 3, 4, 2],
    ![1, 0, 4, 2, 3],
    ![1, 0, 4, 3, 2],
    ![1, 2, 0, 3, 4],
    ![1, 2, 0, 4, 3],
    ![1, 2, 3, 0, 4],
    ![1, 2, 3, 4, 0],
    ![1, 2, 4, 0, 3],
    ![1, 2, 4, 3, 0],
    ![1, 3, 0, 2, 4],
    ![1, 3, 0, 4, 2],
    ![1, 3, 2, 0, 4],
    ![1, 3, 2, 4, 0],
    ![1, 3, 4, 0, 2],
    ![1, 3, 4, 2, 0],
    ![1, 4, 0, 2, 3],
    ![1, 4, 0, 3, 2],
    ![1, 4, 2, 0, 3],
    ![1, 4, 2, 3, 0],
    ![1, 4, 3, 0, 2],
    ![1, 4, 3, 2, 0],
    ![2, 0, 1, 3, 4],
    ![2, 0, 1, 4, 3],
    ![2, 0, 3, 1, 4],
    ![2, 0, 3, 4, 1],
    ![2, 0, 4, 1, 3],
    ![2, 0, 4, 3, 1],
    ![2, 1, 0, 3, 4],
    ![2, 1, 0, 4, 3],
    ![2, 1, 3, 0, 4],
    ![2, 1, 3, 4, 0],
    ![2, 1, 4, 0, 3],
    ![2, 1, 4, 3, 0],
    ![2, 3, 0, 1, 4],
    ![2, 3, 0, 4, 1],
    ![2, 3, 1, 0, 4],
    ![2, 3, 1, 4, 0],
    ![2, 3, 4, 0, 1],
    ![2, 3, 4, 1, 0],
    ![2, 4, 0, 1, 3],
    ![2, 4, 0, 3, 1],
    ![2, 4, 1, 0, 3],
    ![2, 4, 1, 3, 0],
    ![2, 4, 3, 0, 1],
    ![2, 4, 3, 1, 0],
    ![3, 0, 1, 2, 4],
    ![3, 0, 1, 4, 2],
    ![3, 0, 2, 1, 4],
    ![3, 0, 2, 4, 1],
    ![3, 0, 4, 1, 2],
    ![3, 0, 4, 2, 1],
    ![3, 1, 0, 2, 4],
    ![3, 1, 0, 4, 2],
    ![3, 1, 2, 0, 4],
    ![3, 1, 2, 4, 0],
    ![3, 1, 4, 0, 2],
    ![3, 1, 4, 2, 0],
    ![3, 2, 0, 1, 4],
    ![3, 2, 0, 4, 1],
    ![3, 2, 1, 0, 4],
    ![3, 2, 1, 4, 0],
    ![3, 2, 4, 0, 1],
    ![3, 2, 4, 1, 0],
    ![3, 4, 0, 1, 2],
    ![3, 4, 0, 2, 1],
    ![3, 4, 1, 0, 2],
    ![3, 4, 1, 2, 0],
    ![3, 4, 2, 0, 1],
    ![3, 4, 2, 1, 0],
    ![4, 0, 1, 2, 3],
    ![4, 0, 1, 3, 2],
    ![4, 0, 2, 1, 3],
    ![4, 0, 2, 3, 1],
    ![4, 0, 3, 1, 2],
    ![4, 0, 3, 2, 1],
    ![4, 1, 0, 2, 3],
    ![4, 1, 0, 3, 2],
    ![4, 1, 2, 0, 3],
    ![4, 1, 2, 3, 0],
    ![4, 1, 3, 0, 2],
    ![4, 1, 3, 2, 0],
    ![4, 2, 0, 1, 3],
    ![4, 2, 0, 3, 1],
    ![4, 2, 1, 0, 3],
    ![4, 2, 1, 3, 0],
    ![4, 2, 3, 0, 1],
    ![4, 2, 3, 1, 0],
    ![4, 3, 0, 1, 2],
    ![4, 3, 0, 2, 1],
    ![4, 3, 1, 0, 2],
    ![4, 3, 1, 2, 0],
    ![4, 3, 2, 0, 1],
    ![4, 3, 2, 1, 0]]

theorem certificatePerm5Images_bijective (i : Fin 120) :
    Function.Bijective (certificatePerm5Images i) := by
  fin_cases i <;> decide

def certificatePerm5InverseImages : Fin 120 → Fin 5 → Fin 5 :=
  ![![0, 1, 2, 3, 4],
    ![0, 1, 2, 4, 3],
    ![0, 1, 3, 2, 4],
    ![0, 1, 4, 2, 3],
    ![0, 1, 3, 4, 2],
    ![0, 1, 4, 3, 2],
    ![0, 2, 1, 3, 4],
    ![0, 2, 1, 4, 3],
    ![0, 3, 1, 2, 4],
    ![0, 4, 1, 2, 3],
    ![0, 3, 1, 4, 2],
    ![0, 4, 1, 3, 2],
    ![0, 2, 3, 1, 4],
    ![0, 2, 4, 1, 3],
    ![0, 3, 2, 1, 4],
    ![0, 4, 2, 1, 3],
    ![0, 3, 4, 1, 2],
    ![0, 4, 3, 1, 2],
    ![0, 2, 3, 4, 1],
    ![0, 2, 4, 3, 1],
    ![0, 3, 2, 4, 1],
    ![0, 4, 2, 3, 1],
    ![0, 3, 4, 2, 1],
    ![0, 4, 3, 2, 1],
    ![1, 0, 2, 3, 4],
    ![1, 0, 2, 4, 3],
    ![1, 0, 3, 2, 4],
    ![1, 0, 4, 2, 3],
    ![1, 0, 3, 4, 2],
    ![1, 0, 4, 3, 2],
    ![2, 0, 1, 3, 4],
    ![2, 0, 1, 4, 3],
    ![3, 0, 1, 2, 4],
    ![4, 0, 1, 2, 3],
    ![3, 0, 1, 4, 2],
    ![4, 0, 1, 3, 2],
    ![2, 0, 3, 1, 4],
    ![2, 0, 4, 1, 3],
    ![3, 0, 2, 1, 4],
    ![4, 0, 2, 1, 3],
    ![3, 0, 4, 1, 2],
    ![4, 0, 3, 1, 2],
    ![2, 0, 3, 4, 1],
    ![2, 0, 4, 3, 1],
    ![3, 0, 2, 4, 1],
    ![4, 0, 2, 3, 1],
    ![3, 0, 4, 2, 1],
    ![4, 0, 3, 2, 1],
    ![1, 2, 0, 3, 4],
    ![1, 2, 0, 4, 3],
    ![1, 3, 0, 2, 4],
    ![1, 4, 0, 2, 3],
    ![1, 3, 0, 4, 2],
    ![1, 4, 0, 3, 2],
    ![2, 1, 0, 3, 4],
    ![2, 1, 0, 4, 3],
    ![3, 1, 0, 2, 4],
    ![4, 1, 0, 2, 3],
    ![3, 1, 0, 4, 2],
    ![4, 1, 0, 3, 2],
    ![2, 3, 0, 1, 4],
    ![2, 4, 0, 1, 3],
    ![3, 2, 0, 1, 4],
    ![4, 2, 0, 1, 3],
    ![3, 4, 0, 1, 2],
    ![4, 3, 0, 1, 2],
    ![2, 3, 0, 4, 1],
    ![2, 4, 0, 3, 1],
    ![3, 2, 0, 4, 1],
    ![4, 2, 0, 3, 1],
    ![3, 4, 0, 2, 1],
    ![4, 3, 0, 2, 1],
    ![1, 2, 3, 0, 4],
    ![1, 2, 4, 0, 3],
    ![1, 3, 2, 0, 4],
    ![1, 4, 2, 0, 3],
    ![1, 3, 4, 0, 2],
    ![1, 4, 3, 0, 2],
    ![2, 1, 3, 0, 4],
    ![2, 1, 4, 0, 3],
    ![3, 1, 2, 0, 4],
    ![4, 1, 2, 0, 3],
    ![3, 1, 4, 0, 2],
    ![4, 1, 3, 0, 2],
    ![2, 3, 1, 0, 4],
    ![2, 4, 1, 0, 3],
    ![3, 2, 1, 0, 4],
    ![4, 2, 1, 0, 3],
    ![3, 4, 1, 0, 2],
    ![4, 3, 1, 0, 2],
    ![2, 3, 4, 0, 1],
    ![2, 4, 3, 0, 1],
    ![3, 2, 4, 0, 1],
    ![4, 2, 3, 0, 1],
    ![3, 4, 2, 0, 1],
    ![4, 3, 2, 0, 1],
    ![1, 2, 3, 4, 0],
    ![1, 2, 4, 3, 0],
    ![1, 3, 2, 4, 0],
    ![1, 4, 2, 3, 0],
    ![1, 3, 4, 2, 0],
    ![1, 4, 3, 2, 0],
    ![2, 1, 3, 4, 0],
    ![2, 1, 4, 3, 0],
    ![3, 1, 2, 4, 0],
    ![4, 1, 2, 3, 0],
    ![3, 1, 4, 2, 0],
    ![4, 1, 3, 2, 0],
    ![2, 3, 1, 4, 0],
    ![2, 4, 1, 3, 0],
    ![3, 2, 1, 4, 0],
    ![4, 2, 1, 3, 0],
    ![3, 4, 1, 2, 0],
    ![4, 3, 1, 2, 0],
    ![2, 3, 4, 1, 0],
    ![2, 4, 3, 1, 0],
    ![3, 2, 4, 1, 0],
    ![4, 2, 3, 1, 0],
    ![3, 4, 2, 1, 0],
    ![4, 3, 2, 1, 0]]

def certificatePerm5 (i : Fin 120) : Equiv.Perm (Fin 5) where
  toFun := certificatePerm5Images i
  invFun := certificatePerm5InverseImages i
  left_inv := by fin_cases i <;> decide
  right_inv := by fin_cases i <;> decide

theorem certificatePerm5_apply (i : Fin 120) (j : Fin 5) :
    certificatePerm5 i j = certificatePerm5Images i j := rfl

theorem certificatePerm5_bijective : Function.Bijective certificatePerm5 := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · intro i j h
    have hi : Function.Injective certificatePerm5Images := by decide
    apply hi
    funext k
    exact Equiv.congr_fun h k
  · norm_num [Fintype.card_perm, Nat.factorial]

theorem certificate_sum_perm5 {M : Type*} [AddCommMonoid M]
    (f : Equiv.Perm (Fin 5) → M) :
    (∑ σ, f σ) = ∑ i : Fin 120, f (certificatePerm5 i) := by
  symm
  exact Fintype.sum_equiv (Equiv.ofBijective certificatePerm5
    certificatePerm5_bijective) _ _ (fun _ => rfl)

end ThreeCopyQutritWerner
