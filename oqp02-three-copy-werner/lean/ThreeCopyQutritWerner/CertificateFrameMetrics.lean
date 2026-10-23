module

public import ThreeCopyQutritWerner.CertificateLocalFramesChecks
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Data.Complex.Basic
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.GroupTheory.QuotientGroup.ModEq
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Topology.Semicontinuity.Hemicontinuity
public import Mathlib.Topology.WithTopology

@[expose] public section


/-!
# Exact positivity of original local metrics from coordinate left inverses

A local frame that contains an identity row submatrix is injective over every
semiring. Over the complex numbers its original Gram matrix is therefore
positive definite. This avoids computing large determinants and retains the
actual archive metric, rather than replacing it by a Euclidean one.
-/

open scoped Matrix ComplexOrder

namespace ThreeCopyQutritWerner

/-- An explicitly selected identity submatrix proves frame injectivity. -/
theorem certificateFrame_injective_of_coordinate_left_inverse
    {n m R : Type*} [Fintype m] [DecidableEq m] [Semiring R]
    (U : Matrix n m R) (pivots : m → n) (hp : U.submatrix pivots id = 1) :
    Function.Injective U.mulVec := by
  intro x y h
  have h' := congrArg (fun f : n → R => fun i : m => f (pivots i)) h
  change (U.submatrix pivots id) *ᵥ x = (U.submatrix pivots id) *ᵥ y at h'
  simpa only [hp, Matrix.one_mulVec] using h'

/-- The integer transpose Gram becomes the physical Hermitian Gram under complex cast. -/
theorem certificateIntGram_cast_complex {n m : Type*} [Fintype n]
    (U : Matrix n m ℤ) :
    (U.map (Int.cast : ℤ → ℂ))ᴴ * U.map (Int.cast : ℤ → ℂ) =
      (Uᵀ * U).map (Int.cast : ℤ → ℂ) := by
  ext i j
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.transpose_apply]

/-- Exact Gram matching and coordinate pivots certify the actual complex local metric. -/
theorem certificateLocalMetric_posDef_of_pivots {n m : Type*}
    [Fintype n] [Fintype m] [DecidableEq m]
    (U : Matrix n m ℤ) (G : Matrix m m ℤ) (pivots : m → n)
    (hG : Uᵀ * U = G) (hp : U.submatrix pivots id = 1) :
    (G.map (Int.cast : ℤ → ℂ)).PosDef := by
  have hpC : (U.map (Int.cast : ℤ → ℂ)).submatrix pivots id = 1 := by
    ext i j
    have h : U (pivots i) j = (1 : Matrix m m ℤ) i j :=
      congrFun (congrFun hp i) j
    simp only [Matrix.submatrix_apply, Matrix.map_apply, id_eq, h]
    simp [Matrix.one_apply]
  have hinj := certificateFrame_injective_of_coordinate_left_inverse
    (U.map (Int.cast : ℤ → ℂ)) pivots hpC
  have hpos := Matrix.PosDef.conjTranspose_mul_self
    (U.map (Int.cast : ℤ → ℂ)) hinj
  rw [certificateIntGram_cast_complex, hG] at hpos
  exact hpos

end ThreeCopyQutritWerner
