module

public import ThreeCopyQutritWerner.CertificateDescendantData

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped Matrix

namespace ThreeCopyQutritWerner

/-- Literal physical source binding for descendant column 48. -/
theorem certificateDescendantColumn2_48_generated_step :
    certificateSparseVector (certificateDescendantColumns2 48) =
      certificateSparseVector (certificateDescendantSeeds2 48) := by
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 49. -/
theorem certificateDescendantColumn2_49_generated_step :
    certificateSparseVector (certificateDescendantColumns2 49) =
      certificateSparseVector (certificateDescendantSeeds2 49) := by
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 50. -/
theorem certificateDescendantColumn2_50_generated_step :
    certificateSparseVector (certificateDescendantColumns2 50) =
      certificateSparseVector (certificateDescendantSeeds2 50) := by
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 51. -/
theorem certificateDescendantColumn2_51_generated_step :
    certificateSparseVector (certificateDescendantColumns2 51) =
      certificateLocalLowering {0} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 0) := by
  change certificateSparseVector (certificateDescendantColumns2 51) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 0)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 52. -/
theorem certificateDescendantColumn2_52_generated_step :
    certificateSparseVector (certificateDescendantColumns2 52) =
      certificateLocalLowering {0} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 0) := by
  change certificateSparseVector (certificateDescendantColumns2 52) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 0)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 53. -/
theorem certificateDescendantColumn2_53_generated_step :
    certificateSparseVector (certificateDescendantColumns2 53) =
      certificateLocalLowering {0} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 1) := by
  change certificateSparseVector (certificateDescendantColumns2 53) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 1)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 54. -/
theorem certificateDescendantColumn2_54_generated_step :
    certificateSparseVector (certificateDescendantColumns2 54) =
      certificateLocalLowering {0} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 1) := by
  change certificateSparseVector (certificateDescendantColumns2 54) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 1)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 55. -/
theorem certificateDescendantColumn2_55_generated_step :
    certificateSparseVector (certificateDescendantColumns2 55) =
      certificateLocalLowering {0} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 2) := by
  change certificateSparseVector (certificateDescendantColumns2 55) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 2)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 56. -/
theorem certificateDescendantColumn2_56_generated_step :
    certificateSparseVector (certificateDescendantColumns2 56) =
      certificateLocalLowering {0} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 2) := by
  change certificateSparseVector (certificateDescendantColumns2 56) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 2)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 57. -/
theorem certificateDescendantColumn2_57_generated_step :
    certificateSparseVector (certificateDescendantColumns2 57) =
      certificateLocalLowering {0} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 3) := by
  change certificateSparseVector (certificateDescendantColumns2 57) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 3)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 58. -/
theorem certificateDescendantColumn2_58_generated_step :
    certificateSparseVector (certificateDescendantColumns2 58) =
      certificateLocalLowering {0} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 3) := by
  change certificateSparseVector (certificateDescendantColumns2 58) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 3)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 59. -/
theorem certificateDescendantColumn2_59_generated_step :
    certificateSparseVector (certificateDescendantColumns2 59) =
      certificateLocalLowering {0} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 4) := by
  change certificateSparseVector (certificateDescendantColumns2 59) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 4)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 60. -/
theorem certificateDescendantColumn2_60_generated_step :
    certificateSparseVector (certificateDescendantColumns2 60) =
      certificateLocalLowering {0} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 4) := by
  change certificateSparseVector (certificateDescendantColumns2 60) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 4)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 61. -/
theorem certificateDescendantColumn2_61_generated_step :
    certificateSparseVector (certificateDescendantColumns2 61) =
      certificateLocalLowering {0} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 5) := by
  change certificateSparseVector (certificateDescendantColumns2 61) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 5)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 62. -/
theorem certificateDescendantColumn2_62_generated_step :
    certificateSparseVector (certificateDescendantColumns2 62) =
      certificateLocalLowering {0} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 6) := by
  change certificateSparseVector (certificateDescendantColumns2 62) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 6)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 63. -/
theorem certificateDescendantColumn2_63_generated_step :
    certificateSparseVector (certificateDescendantColumns2 63) =
      certificateLocalLowering {0} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 7) := by
  change certificateSparseVector (certificateDescendantColumns2 63) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 7)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 64. -/
theorem certificateDescendantColumn2_64_generated_step :
    certificateSparseVector (certificateDescendantColumns2 64) =
      certificateLocalLowering {0} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 8) := by
  change certificateSparseVector (certificateDescendantColumns2 64) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 8)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 65. -/
theorem certificateDescendantColumn2_65_generated_step :
    certificateSparseVector (certificateDescendantColumns2 65) =
      certificateLocalLowering {0} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 9) := by
  change certificateSparseVector (certificateDescendantColumns2 65) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 9)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 66. -/
theorem certificateDescendantColumn2_66_generated_step :
    certificateSparseVector (certificateDescendantColumns2 66) =
      certificateLocalLowering {0} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 10) := by
  change certificateSparseVector (certificateDescendantColumns2 66) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 10)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 67. -/
theorem certificateDescendantColumn2_67_generated_step :
    certificateSparseVector (certificateDescendantColumns2 67) =
      certificateLocalLowering {0} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 10) := by
  change certificateSparseVector (certificateDescendantColumns2 67) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 10)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 68. -/
theorem certificateDescendantColumn2_68_generated_step :
    certificateSparseVector (certificateDescendantColumns2 68) =
      certificateLocalLowering {0} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 11) := by
  change certificateSparseVector (certificateDescendantColumns2 68) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 11)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 69. -/
theorem certificateDescendantColumn2_69_generated_step :
    certificateSparseVector (certificateDescendantColumns2 69) =
      certificateLocalLowering {0} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 11) := by
  change certificateSparseVector (certificateDescendantColumns2 69) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 11)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 70. -/
theorem certificateDescendantColumn2_70_generated_step :
    certificateSparseVector (certificateDescendantColumns2 70) =
      certificateLocalLowering {0} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 12) := by
  change certificateSparseVector (certificateDescendantColumns2 70) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 12)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 71. -/
theorem certificateDescendantColumn2_71_generated_step :
    certificateSparseVector (certificateDescendantColumns2 71) =
      certificateLocalLowering {0} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 12) := by
  change certificateSparseVector (certificateDescendantColumns2 71) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 12)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

end ThreeCopyQutritWerner
