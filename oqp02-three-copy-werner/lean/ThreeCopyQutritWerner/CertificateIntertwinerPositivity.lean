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
# Positivity transported through a spanning weighted intertwiner

A physical Hermitian operator can be recovered from invariant generating
frames without identifying the entire descendant Gram matrix. The coefficient
operator has its original positive metric G, and its quadratic-form matrix D
is positive semidefinite. A surjective intertwiner transfers that positivity.
No Euclidean positivity of G⁻¹D is assumed.
-/

noncomputable section

open scoped Matrix ComplexOrder

namespace ThreeCopyQutritWerner

/-- The adjoint of a surjective rectangular matrix kills no nonzero vector. -/
theorem certificate_adjoint_mulVec_ne_zero_of_surjective
    {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n]
    (S : Matrix n m ℂ) (hS : Function.Surjective S.mulVec)
    {v : n → ℂ} (hv : v ≠ 0) : Sᴴ *ᵥ v ≠ 0 := by
  obtain ⟨T, hT⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp hS
  intro hz
  apply hv
  have h := congrArg (fun A : Matrix n n ℂ => A *ᵥ v)
    (congrArg Matrix.conjTranspose hT)
  simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_one,
    ← Matrix.mulVec_mulVec, hz, Matrix.mulVec_zero, Matrix.one_mulVec] using h.symm

/-- A surjective intertwiner from a positive operator in a positive metric
forces a Hermitian physical operator to be positive semidefinite. -/
theorem certificate_posSemidef_of_weighted_intertwiner
    {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (M : Matrix n n ℂ) (S : Matrix n m ℂ) (G D : Matrix m m ℂ)
    (hM : M.IsHermitian) (hS : Function.Surjective S.mulVec)
    (hG : G.PosDef) (hD : D.PosSemidef)
    (hinter : M * S = S * (G⁻¹ * D)) : M.PosSemidef := by
  apply hM.posSemidef_iff_eigenvalues_nonneg.mpr
  intro i
  let v : n → ℂ := ⇑(hM.eigenvectorBasis i)
  have hv : v ≠ 0 :=
    (WithLp.ofLp_eq_zero 2).ne.2 (hM.eigenvectorBasis.orthonormal.ne_zero i)
  let y : m → ℂ := Sᴴ *ᵥ v
  have hy : y ≠ 0 := certificate_adjoint_mulVec_ne_zero_of_surjective S hS hv
  let x : m → ℂ := G⁻¹ *ᵥ y
  have hGx : G *ᵥ x = y := by
    dsimp only [x]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv G
      ((Matrix.isUnit_iff_isUnit_det G).mp hG.isUnit), Matrix.one_mulVec]
  have hx : x ≠ 0 := by
    intro hz
    apply hy
    rw [← hGx, hz, Matrix.mulVec_zero]
  have hadj : Sᴴ * M = (D * G⁻¹) * Sᴴ := by
    have h := congrArg Matrix.conjTranspose hinter
    simpa only [Matrix.conjTranspose_mul, hM.eq, hD.isHermitian.eq,
      hG.inv.isHermitian.eq] using h
  have hDx : D *ᵥ x = hM.eigenvalues i • y := by
    dsimp only [x, y, v]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hadj,
      ← Matrix.mulVec_mulVec, hM.mulVec_eigenvectorBasis, Matrix.mulVec_smul]
  have hp := hG.re_dotProduct_pos hx
  have hn := hD.re_dotProduct_nonneg x
  rw [hDx, ← hGx, dotProduct_smul, RCLike.smul_re] at hn
  exact nonneg_of_mul_nonneg_left hn hp

end ThreeCopyQutritWerner
