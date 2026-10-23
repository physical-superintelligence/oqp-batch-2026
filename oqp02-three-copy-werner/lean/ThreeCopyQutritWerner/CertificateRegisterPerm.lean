module

public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Data.List.Enum
public import Mathlib.GroupTheory.QuotientGroup.ModEq
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Topology.WithTopology

@[expose] public section


/-! Register permutation alone, without the concrete six-register endpoint carrier.
The definition and inverse theorem are moved verbatim from CertificateProjector. -/

noncomputable section
namespace ThreeCopyQutritWerner

/-- Relabel the tensor coordinates by a permutation of the whole registers. -/
def certificateRegisterPerm {k : ℕ} {n : Type*} (σ : Equiv.Perm (Fin k)) :
    Equiv.Perm (Fin k → n) where
  toFun r i := r (σ i)
  invFun r i := r (σ⁻¹ i)
  left_inv r := by funext i; simp
  right_inv r := by funext i; simp

theorem certificateRegisterPerm_inv {k : ℕ} {n : Type*} (σ : Equiv.Perm (Fin k)) :
    (certificateRegisterPerm (n := n) σ)⁻¹ = certificateRegisterPerm σ⁻¹ := rfl

end ThreeCopyQutritWerner
