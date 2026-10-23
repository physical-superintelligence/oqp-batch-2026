module

public import ThreeCopyQutritWerner.CertificateDescendantCompleteness
public import ThreeCopyQutritWerner.CertificateDescendantProgram
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Data.Complex.Basic
public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Polynomial.Monomial
public import Mathlib.Data.Fintype.Order
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence

@[expose] public section


/-!
# Physical completeness of the exact sector-2 descendants

The full 729-dimensional complex space is spanned by literal physical columns.
Every such integer column is separately bound to a finite product of the signed
lowering matrices on an original archive highest-frame column. No Weyl dimension,
operator commutation, certificate positivity, or endpoint inequality is assumed.
-/

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

/-- An exact right inverse stays a right inverse under a scalar ring homomorphism. -/
theorem certificateMatrix_surjective_map {n m R S : Type*}
    [Fintype n] [Fintype m] [DecidableEq n] [Semiring R] [Semiring S]
    (f : R →+* S) (M : Matrix n m R) (hM : Function.Surjective M.mulVec) :
    Function.Surjective (M.map f).mulVec := by
  obtain ⟨B, hB⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp hM
  apply Matrix.mulVec_surjective_iff_exists_right_inverse.mpr
  refine ⟨B.map f, ?_⟩
  rw [← Matrix.map_mul, hB]
  exact Matrix.map_one _ (map_zero f) (map_one f)

/-- The 729 literal physical descendant columns span the full complex local space. -/
theorem certificateDescendantPhysical2_complex_surjective :
    Function.Surjective (certificateDescendantPhysical2.map (Int.cast : ℤ → ℂ)).mulVec := by
  classical
  have h := certificateMatrix_surjective_map (Rat.castHom ℂ)
    (certificateDescendantPhysical2.map (Int.cast : ℤ → ℚ))
    certificateDescendantPhysical2_surjective
  have hcast : (certificateDescendantPhysical2.map (Int.cast : ℤ → ℚ)).map (Rat.castHom ℂ) =
      certificateDescendantPhysical2.map (Int.cast : ℤ → ℂ) := by
    ext i j
    simp
  rwa [hcast] at h

/-- Each physical spanning column is an actual lowering descendant of a source-bound
highest-frame column, with its integer coordinates and register order retained. -/
theorem certificateDescendantPhysical2_generated (j : CertificateDescendantIndex2) :
    ∃ s : Fin 51, ∃ word : List (Fin 2),
      (fun w => certificateDescendantPhysical2 w j) =
        word.foldl (fun x g => certificateLocalLowering {0} g *ᵥ x)
          (certificateSparseVector (certificateDescendantSeeds2 s)) :=
  certificateDescendantColumns2_generated (certificateDescendantBlockColumns2 j.1 j.2)

/-- Combined physical spanning and exact generation certificate for signed sector 2. -/
theorem certificateDescendantPhysical2_complete :
    Function.Surjective (certificateDescendantPhysical2.map (Int.cast : ℤ → ℂ)).mulVec ∧
      ∀ j : CertificateDescendantIndex2, ∃ s : Fin 51, ∃ word : List (Fin 2),
        (fun w => certificateDescendantPhysical2 w j) =
          word.foldl (fun x g => certificateLocalLowering {0} g *ᵥ x)
            (certificateSparseVector (certificateDescendantSeeds2 s)) :=
  ⟨certificateDescendantPhysical2_complex_surjective, certificateDescendantPhysical2_generated⟩

end ThreeCopyQutritWerner
