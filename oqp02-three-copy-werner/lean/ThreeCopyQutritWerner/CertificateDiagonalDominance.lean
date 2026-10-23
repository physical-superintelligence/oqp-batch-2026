module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.LinearAlgebra.Matrix.Gershgorin
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Abel
public import Mathlib.Algebra.Algebra.Spectrum.Pi
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Module.Basic
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
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
public import Mathlib.Topology.ContinuousMap.Units
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Topology.Semicontinuity.Hemicontinuity
public import Mathlib.Topology.WithTopology

@[expose] public section


/-!
# Exact row-dominance witnesses for native trial margins

A rational approximate factor is only a proposed witness. Positivity follows
from an exact residual and exact row inequalities. These generic results do
not assert that any archived trial block satisfies those finite checks.
-/

noncomputable section

open scoped BigOperators Matrix ComplexOrder

namespace ThreeCopyQutritWerner

variable {n k : Type*} [Fintype n] [Fintype k] [DecidableEq n]

/-- The actual Hermitian eigenvalues lie above any exact row Gershgorin floor. -/
theorem certificate_eigenvalues_ge_of_row_dominance
    (A : Matrix n n ℂ) (hA : A.IsHermitian) (gamma : ℝ)
    (hrow : ∀ i, gamma + ∑ j ∈ Finset.univ.erase i, ‖A i j‖ ≤ (A i i).re)
    (i : n) : gamma ≤ hA.eigenvalues i := by
  have hv : Module.End.HasEigenvector (Matrix.toLin' A)
      (hA.eigenvalues i : ℂ) (⇑(hA.eigenvectorBasis i)) := by
    refine ⟨?_, (WithLp.ofLp_eq_zero 2).ne.2 (hA.eigenvectorBasis.orthonormal.ne_zero i)⟩
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
    ext j
    simpa only [Pi.smul_apply, RCLike.real_smul_eq_coe_mul, smul_eq_mul] using!
      congrFun (hA.mulVec_eigenvectorBasis i) j
  obtain ⟨j, hj⟩ := eigenvalue_mem_ball (Module.End.hasEigenvalue_of_hasEigenvector hv)
  rw [mem_closedBall_iff_norm'] at hj
  have hre := (Complex.re_le_norm (A j j - (hA.eigenvalues i : ℂ))).trans hj
  simp only [Complex.sub_re, Complex.ofReal_re] at hre
  linarith [hrow j]

/-- An actual Hermitian row-dominant matrix with nonnegative diagonal slack is PSD. -/
theorem certificate_posSemidef_of_row_dominance
    (A : Matrix n n ℂ) (hA : A.IsHermitian)
    (hrow : ∀ i, ∑ j ∈ Finset.univ.erase i, ‖A i j‖ ≤ (A i i).re) :
    A.PosSemidef := by
  apply hA.posSemidef_iff_eigenvalues_nonneg.mpr
  intro i
  exact certificate_eigenvalues_ge_of_row_dominance A hA 0
    (by simpa only [zero_add] using hrow) i

/-- Exact integer row inequalities are enough after the literal complex cast. -/
theorem certificate_integer_posSemidef_of_row_dominance
    (A : Matrix n n ℤ) (hsym : Aᵀ = A)
    (hrow : ∀ i, ∑ j ∈ Finset.univ.erase i, |A i j| ≤ A i i) :
    (A.map (Int.castRingHom ℂ)).PosSemidef := by
  apply certificate_posSemidef_of_row_dominance
  · ext i j
    have h : A j i = A i j := congrFun (congrFun hsym i) j
    change star (A j i : ℂ) = (A i j : ℂ)
    simpa only [star_intCast] using congrArg (fun z : ℤ => (z : ℂ)) h
  · intro i
    have h : (∑ j ∈ Finset.univ.erase i, |(A i j : ℝ)|) ≤ (A i i : ℝ) := by
      exact_mod_cast hrow i
    simpa [Matrix.map_apply, Complex.norm_intCast] using h

/-- If an exact Gram residual lies above gamma times the identity by row
bounds, the original specified matrix has the same positive-semidefinite floor.
The proposed factor C has no approximation or numerical-correctness premise. -/
theorem certificate_margin_of_gram_residual
    (M : Matrix n n ℂ) (C : Matrix n k ℂ) (gamma : ℝ)
    (hM : M.IsHermitian)
    (hrow : ∀ i,
      ∑ j ∈ Finset.univ.erase i,
        ‖(M - C * Cᴴ - (gamma : ℂ) • (1 : Matrix n n ℂ)) i j‖ ≤
      ((M - C * Cᴴ - (gamma : ℂ) • (1 : Matrix n n ℂ)) i i).re) :
    (M - (gamma : ℂ) • (1 : Matrix n n ℂ)).PosSemidef := by
  have hg : ((gamma : ℂ) • (1 : Matrix n n ℂ)).IsHermitian := by
    exact Matrix.isHermitian_one.smul
      ((Complex.im_eq_zero_iff_isSelfAdjoint _).mp (by simp))
  have hR := certificate_posSemidef_of_row_dominance
    (M - C * Cᴴ - (gamma : ℂ) • (1 : Matrix n n ℂ))
    ((hM.sub (Matrix.isHermitian_mul_conjTranspose_self C)).sub hg) hrow
  have h := hR.add (Matrix.posSemidef_self_mul_conjTranspose C)
  convert h using 1 <;> abel

end ThreeCopyQutritWerner
