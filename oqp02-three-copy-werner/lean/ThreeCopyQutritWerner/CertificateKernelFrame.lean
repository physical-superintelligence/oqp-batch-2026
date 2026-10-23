module

public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Data.List.Enum
public import Mathlib.GroupTheory.QuotientGroup.ModEq
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Topology.Semicontinuity.Hemicontinuity
public import Mathlib.Topology.WithTopology

@[expose] public section


/-!
# Exact kernel certificates and the original highest-weight metric

The finite certificate `d • (1 - U * P) = W * R` proves that every vector
annihilated by the selected raising tests `R` lies in the original frame `U`.
`P` retains the original pivot coordinates. The coefficient action of an
operator preserving that kernel is therefore recovered, rather than assumed.
Its quadratic-form matrix is the compression in the original Gram metric.

Concrete weight support and selected raising rows are separate obligations.
-/

noncomputable section

open scoped Matrix ComplexOrder

namespace ThreeCopyQutritWerner

section ExactKernel

variable {K n m q c : Type*} [CommRing K] [IsDomain K]
  [Fintype n] [Fintype m] [Fintype q] [DecidableEq n]

/-- A scaled integer or field certificate reconstructs every annihilated column. -/
theorem certificate_kernelFrame_reconstruct
    (U : Matrix n m K) (P : Matrix m n K)
    (R : Matrix q n K) (W : Matrix n q K)
    (d : K) (hd : d ≠ 0)
    (hcert : d • (1 - U * P) = W * R)
    (X : Matrix n c K) (hRX : R * X = 0) :
    X = U * (P * X) := by
  have hz : d • (X - U * (P * X)) = 0 := calc
    d • (X - U * (P * X)) = (d • (1 - U * P)) * X := by
      simp only [Matrix.smul_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
    _ = (W * R) * X := by rw [hcert]
    _ = 0 := by rw [Matrix.mul_assoc, hRX, Matrix.mul_zero]
  ext i j
  apply sub_eq_zero.mp
  have hij : d * (X i j - (U * (P * X)) i j) = 0 :=
    congrFun (congrFun hz i) j
  exact (mul_eq_zero.mp hij).resolve_left hd

/-- The unscaled form is convenient after mapping an exact certificate to a field. -/
theorem certificate_kernelFrame_reconstruct_unscaled
    (U : Matrix n m K) (P : Matrix m n K)
    (R : Matrix q n K) (L : Matrix n q K)
    (hcert : 1 - U * P = L * R)
    (X : Matrix n c K) (hRX : R * X = 0) :
    X = U * (P * X) :=
  certificate_kernelFrame_reconstruct U P R L 1 one_ne_zero
    (by simpa only [one_smul] using hcert) X hRX

/-- The same exact certificate reconstructs individual physical vectors. -/
theorem certificate_kernelFrame_reconstruct_vector
    (U : Matrix n m K) (P : Matrix m n K)
    (R : Matrix q n K) (W : Matrix n q K)
    (d : K) (hd : d ≠ 0)
    (hcert : d • (1 - U * P) = W * R)
    (x : n → K) (hRx : R *ᵥ x = 0) :
    x = U *ᵥ (P *ᵥ x) := by
  have hz : d • (x - U *ᵥ (P *ᵥ x)) = 0 := calc
    d • (x - U *ᵥ (P *ᵥ x)) = (d • (1 - U * P)) *ᵥ x := by
      simp only [Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
        Matrix.mulVec_mulVec]
    _ = (W * R) *ᵥ x := by rw [hcert]
    _ = 0 := by rw [← Matrix.mulVec_mulVec, hRx, Matrix.mulVec_zero]
  ext i
  apply sub_eq_zero.mp
  have hi : d * (x i - (U *ᵥ (P *ᵥ x)) i) = 0 := congrFun hz i
  exact (mul_eq_zero.mp hi).resolve_left hd

/-- Both finite identities identify the selected-test kernel with the frame range. -/
theorem certificate_kernelFrame_kernel_iff
    (U : Matrix n m K) (P : Matrix m n K)
    (R : Matrix q n K) (W : Matrix n q K)
    (d : K) (hd : d ≠ 0)
    (hcert : d • (1 - U * P) = W * R) (hRU : R * U = 0)
    (x : n → K) :
    R *ᵥ x = 0 ↔ ∃ a : m → K, U *ᵥ a = x := by
  constructor
  · intro hx
    exact ⟨P *ᵥ x,
      (certificate_kernelFrame_reconstruct_vector U P R W d hd hcert x hx).symm⟩
  · rintro ⟨a, rfl⟩
    rw [Matrix.mulVec_mulVec, hRU, Matrix.zero_mulVec]

/-- The operator's actual pivot coordinates determine its action on the frame. -/
theorem certificate_kernelFrame_source_action
    (U : Matrix n m K) (P : Matrix m n K)
    (R : Matrix q n K) (W : Matrix n q K)
    (d : K) (hd : d ≠ 0)
    (hcert : d • (1 - U * P) = W * R)
    (M : Matrix n n K) (hRMU : R * (M * U) = 0) :
    M * U = U * (P * (M * U)) :=
  certificate_kernelFrame_reconstruct U P R W d hd hcert (M * U) hRMU

end ExactKernel

/-- Original physical compression equals original Gram metric times recovered action. -/
theorem certificate_kernelFrame_compression
    {n m : Type*} [Fintype n] [Fintype m]
    (U : Matrix n m ℂ) (P : Matrix m n ℂ) (M : Matrix n n ℂ)
    (hact : M * U = U * (P * (M * U))) :
    Uᴴ * M * U = (Uᴴ * U) * (P * (M * U)) := by
  calc
    Uᴴ * M * U = Uᴴ * (M * U) := Matrix.mul_assoc _ _ _
    _ = Uᴴ * (U * (P * (M * U))) := congrArg (fun X => Uᴴ * X) hact
    _ = (Uᴴ * U) * (P * (M * U)) := (Matrix.mul_assoc _ _ _).symm

/-- In the positive original metric, the recovered action is exactly `G⁻¹ D`. -/
theorem certificate_kernelFrame_weighted_action
    {n m : Type*} [Fintype n] [Fintype m] [DecidableEq m]
    (U : Matrix n m ℂ) (P : Matrix m n ℂ) (M : Matrix n n ℂ)
    (hact : M * U = U * (P * (M * U)))
    (hG : (Uᴴ * U).PosDef) :
    M * U = U * ((Uᴴ * U)⁻¹ * (Uᴴ * M * U)) := by
  have hcomp := certificate_kernelFrame_compression U P M hact
  rw [hcomp, Matrix.nonsing_inv_mul_cancel_left _ _
    ((Matrix.isUnit_iff_isUnit_det _).mp hG.isUnit)]
  exact hact

end ThreeCopyQutritWerner
