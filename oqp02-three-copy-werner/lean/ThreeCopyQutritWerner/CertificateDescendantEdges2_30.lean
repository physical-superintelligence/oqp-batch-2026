module

public import ThreeCopyQutritWerner.CertificateDescendantData

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped Matrix

namespace ThreeCopyQutritWerner

/-- Literal physical source binding for descendant column 720. -/
theorem certificateDescendantColumn2_720_generated_step :
    certificateSparseVector (certificateDescendantColumns2 720) =
      certificateLocalLowering {0} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 708) := by
  change certificateSparseVector (certificateDescendantColumns2 720) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 708)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 721. -/
theorem certificateDescendantColumn2_721_generated_step :
    certificateSparseVector (certificateDescendantColumns2 721) =
      certificateLocalLowering {0} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 710) := by
  change certificateSparseVector (certificateDescendantColumns2 721) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 710)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 722. -/
theorem certificateDescendantColumn2_722_generated_step :
    certificateSparseVector (certificateDescendantColumns2 722) =
      certificateLocalLowering {0} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 711) := by
  change certificateSparseVector (certificateDescendantColumns2 722) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 711)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 723. -/
theorem certificateDescendantColumn2_723_generated_step :
    certificateSparseVector (certificateDescendantColumns2 723) =
      certificateLocalLowering {0} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 713) := by
  change certificateSparseVector (certificateDescendantColumns2 723) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 713)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 724. -/
theorem certificateDescendantColumn2_724_generated_step :
    certificateSparseVector (certificateDescendantColumns2 724) =
      certificateLocalLowering {0} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 715) := by
  change certificateSparseVector (certificateDescendantColumns2 724) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 715)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 725. -/
theorem certificateDescendantColumn2_725_generated_step :
    certificateSparseVector (certificateDescendantColumns2 725) =
      certificateLocalLowering {0} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 717) := by
  change certificateSparseVector (certificateDescendantColumns2 725) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 717)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 726. -/
theorem certificateDescendantColumn2_726_generated_step :
    certificateSparseVector (certificateDescendantColumns2 726) =
      certificateLocalLowering {0} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 719) := by
  change certificateSparseVector (certificateDescendantColumns2 726) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 719)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 727. -/
theorem certificateDescendantColumn2_727_generated_step :
    certificateSparseVector (certificateDescendantColumns2 727) =
      certificateLocalLowering {0} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 719) := by
  change certificateSparseVector (certificateDescendantColumns2 727) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 719)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 728. -/
theorem certificateDescendantColumn2_728_generated_step :
    certificateSparseVector (certificateDescendantColumns2 728) =
      certificateLocalLowering {0} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 726) := by
  change certificateSparseVector (certificateDescendantColumns2 728) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 726)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

end ThreeCopyQutritWerner
