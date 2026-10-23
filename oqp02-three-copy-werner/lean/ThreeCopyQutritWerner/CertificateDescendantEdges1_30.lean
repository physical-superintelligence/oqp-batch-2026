module

public import ThreeCopyQutritWerner.CertificateDescendantData1

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped Matrix

namespace ThreeCopyQutritWerner

/-- Literal physical source binding for descendant column 720. -/
theorem certificateDescendantColumn1_720_generated_step :
    certificateSparseVector (certificateDescendantColumns1 720) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 706) := by
  change certificateSparseVector (certificateDescendantColumns1 720) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 706)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 721. -/
theorem certificateDescendantColumn1_721_generated_step :
    certificateSparseVector (certificateDescendantColumns1 721) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 708) := by
  change certificateSparseVector (certificateDescendantColumns1 721) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 708)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 722. -/
theorem certificateDescendantColumn1_722_generated_step :
    certificateSparseVector (certificateDescendantColumns1 722) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 710) := by
  change certificateSparseVector (certificateDescendantColumns1 722) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 710)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 723. -/
theorem certificateDescendantColumn1_723_generated_step :
    certificateSparseVector (certificateDescendantColumns1 723) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 712) := by
  change certificateSparseVector (certificateDescendantColumns1 723) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 712)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 724. -/
theorem certificateDescendantColumn1_724_generated_step :
    certificateSparseVector (certificateDescendantColumns1 724) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 714) := by
  change certificateSparseVector (certificateDescendantColumns1 724) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 714)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 725. -/
theorem certificateDescendantColumn1_725_generated_step :
    certificateSparseVector (certificateDescendantColumns1 725) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 716) := by
  change certificateSparseVector (certificateDescendantColumns1 725) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 716)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 726. -/
theorem certificateDescendantColumn1_726_generated_step :
    certificateSparseVector (certificateDescendantColumns1 726) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 718) := by
  change certificateSparseVector (certificateDescendantColumns1 726) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 718)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 727. -/
theorem certificateDescendantColumn1_727_generated_step :
    certificateSparseVector (certificateDescendantColumns1 727) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 719) := by
  change certificateSparseVector (certificateDescendantColumns1 727) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 719)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 728. -/
theorem certificateDescendantColumn1_728_generated_step :
    certificateSparseVector (certificateDescendantColumns1 728) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 726) := by
  change certificateSparseVector (certificateDescendantColumns1 728) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 726)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

end ThreeCopyQutritWerner
