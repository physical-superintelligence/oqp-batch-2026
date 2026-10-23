module

public import ThreeCopyQutritWerner.CertificateDescendantPhysical
public import ThreeCopyQutritWerner.CertificateDescendantCompleteness1
public import ThreeCopyQutritWerner.CertificateDescendantProgram1
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Data.Complex.Basic

@[expose] public section


/-!
# Physical completeness of the exact sector-1 descendants

The full 729-dimensional complex space is spanned by literal physical columns.
Every such integer column is separately bound to a finite product of the signed
lowering matrices on an original archive highest-frame column. No Weyl dimension,
operator commutation, certificate positivity, or endpoint inequality is assumed.
-/

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

/-- The 729 literal physical descendant columns span the full complex local space. -/
theorem certificateDescendantPhysical1_complex_surjective :
    Function.Surjective (certificateDescendantPhysical1.map (Int.cast : ℤ → ℂ)).mulVec := by
  classical
  have h := certificateMatrix_surjective_map (Rat.castHom ℂ)
    (certificateDescendantPhysical1.map (Int.cast : ℤ → ℚ))
    certificateDescendantPhysical1_surjective
  have hcast : (certificateDescendantPhysical1.map (Int.cast : ℤ → ℚ)).map (Rat.castHom ℂ) =
      certificateDescendantPhysical1.map (Int.cast : ℤ → ℂ) := by
    ext i j
    simp
  rwa [hcast] at h

/-- Each physical spanning column is an actual lowering descendant of a source-bound
highest-frame column, with its integer coordinates and register order retained. -/
theorem certificateDescendantPhysical1_generated (j : CertificateDescendantIndex1) :
    ∃ s : Fin 51, ∃ word : List (Fin 2),
      (fun w => certificateDescendantPhysical1 w j) =
        word.foldl (fun x g => certificateLocalLowering {0, 1, 2} g *ᵥ x)
          (certificateSparseVector (certificateDescendantSeeds1 s)) :=
  certificateDescendantColumns1_generated (certificateDescendantBlockColumns1 j.1 j.2)

/-- Combined physical spanning and exact generation certificate for signed sector 1. -/
theorem certificateDescendantPhysical1_complete :
    Function.Surjective (certificateDescendantPhysical1.map (Int.cast : ℤ → ℂ)).mulVec ∧
      ∀ j : CertificateDescendantIndex1, ∃ s : Fin 51, ∃ word : List (Fin 2),
        (fun w => certificateDescendantPhysical1 w j) =
          word.foldl (fun x g => certificateLocalLowering {0, 1, 2} g *ᵥ x)
            (certificateSparseVector (certificateDescendantSeeds1 s)) :=
  ⟨certificateDescendantPhysical1_complex_surjective, certificateDescendantPhysical1_generated⟩

end ThreeCopyQutritWerner
