module

public import ThreeCopyQutritWerner.CertificateDescendantData1

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped Matrix

namespace ThreeCopyQutritWerner

/-- Literal physical source binding for descendant column 48. -/
theorem certificateDescendantColumn1_48_generated_step :
    certificateSparseVector (certificateDescendantColumns1 48) =
      certificateSparseVector (certificateDescendantSeeds1 48) := by
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 49. -/
theorem certificateDescendantColumn1_49_generated_step :
    certificateSparseVector (certificateDescendantColumns1 49) =
      certificateSparseVector (certificateDescendantSeeds1 49) := by
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 50. -/
theorem certificateDescendantColumn1_50_generated_step :
    certificateSparseVector (certificateDescendantColumns1 50) =
      certificateSparseVector (certificateDescendantSeeds1 50) := by
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 51. -/
theorem certificateDescendantColumn1_51_generated_step :
    certificateSparseVector (certificateDescendantColumns1 51) =
      certificateLocalLowering {0, 1, 2} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 0) := by
  change certificateSparseVector (certificateDescendantColumns1 51) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 0)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 52. -/
theorem certificateDescendantColumn1_52_generated_step :
    certificateSparseVector (certificateDescendantColumns1 52) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 0) := by
  change certificateSparseVector (certificateDescendantColumns1 52) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 0)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 53. -/
theorem certificateDescendantColumn1_53_generated_step :
    certificateSparseVector (certificateDescendantColumns1 53) =
      certificateLocalLowering {0, 1, 2} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 1) := by
  change certificateSparseVector (certificateDescendantColumns1 53) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 1)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 54. -/
theorem certificateDescendantColumn1_54_generated_step :
    certificateSparseVector (certificateDescendantColumns1 54) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 1) := by
  change certificateSparseVector (certificateDescendantColumns1 54) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 1)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 55. -/
theorem certificateDescendantColumn1_55_generated_step :
    certificateSparseVector (certificateDescendantColumns1 55) =
      certificateLocalLowering {0, 1, 2} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 2) := by
  change certificateSparseVector (certificateDescendantColumns1 55) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 2)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 56. -/
theorem certificateDescendantColumn1_56_generated_step :
    certificateSparseVector (certificateDescendantColumns1 56) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 2) := by
  change certificateSparseVector (certificateDescendantColumns1 56) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 2)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 57. -/
theorem certificateDescendantColumn1_57_generated_step :
    certificateSparseVector (certificateDescendantColumns1 57) =
      certificateLocalLowering {0, 1, 2} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 3) := by
  change certificateSparseVector (certificateDescendantColumns1 57) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 3)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 58. -/
theorem certificateDescendantColumn1_58_generated_step :
    certificateSparseVector (certificateDescendantColumns1 58) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 3) := by
  change certificateSparseVector (certificateDescendantColumns1 58) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 3)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 59. -/
theorem certificateDescendantColumn1_59_generated_step :
    certificateSparseVector (certificateDescendantColumns1 59) =
      certificateLocalLowering {0, 1, 2} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 4) := by
  change certificateSparseVector (certificateDescendantColumns1 59) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 4)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 60. -/
theorem certificateDescendantColumn1_60_generated_step :
    certificateSparseVector (certificateDescendantColumns1 60) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 4) := by
  change certificateSparseVector (certificateDescendantColumns1 60) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 4)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 61. -/
theorem certificateDescendantColumn1_61_generated_step :
    certificateSparseVector (certificateDescendantColumns1 61) =
      certificateLocalLowering {0, 1, 2} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 5) := by
  change certificateSparseVector (certificateDescendantColumns1 61) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 5)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 62. -/
theorem certificateDescendantColumn1_62_generated_step :
    certificateSparseVector (certificateDescendantColumns1 62) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 5) := by
  change certificateSparseVector (certificateDescendantColumns1 62) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 5)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 63. -/
theorem certificateDescendantColumn1_63_generated_step :
    certificateSparseVector (certificateDescendantColumns1 63) =
      certificateLocalLowering {0, 1, 2} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 6) := by
  change certificateSparseVector (certificateDescendantColumns1 63) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 6)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 64. -/
theorem certificateDescendantColumn1_64_generated_step :
    certificateSparseVector (certificateDescendantColumns1 64) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 6) := by
  change certificateSparseVector (certificateDescendantColumns1 64) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 6)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 65. -/
theorem certificateDescendantColumn1_65_generated_step :
    certificateSparseVector (certificateDescendantColumns1 65) =
      certificateLocalLowering {0, 1, 2} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 7) := by
  change certificateSparseVector (certificateDescendantColumns1 65) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 7)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 66. -/
theorem certificateDescendantColumn1_66_generated_step :
    certificateSparseVector (certificateDescendantColumns1 66) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 7) := by
  change certificateSparseVector (certificateDescendantColumns1 66) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 7)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 67. -/
theorem certificateDescendantColumn1_67_generated_step :
    certificateSparseVector (certificateDescendantColumns1 67) =
      certificateLocalLowering {0, 1, 2} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 8) := by
  change certificateSparseVector (certificateDescendantColumns1 67) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 8)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 68. -/
theorem certificateDescendantColumn1_68_generated_step :
    certificateSparseVector (certificateDescendantColumns1 68) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 8) := by
  change certificateSparseVector (certificateDescendantColumns1 68) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 8)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 69. -/
theorem certificateDescendantColumn1_69_generated_step :
    certificateSparseVector (certificateDescendantColumns1 69) =
      certificateLocalLowering {0, 1, 2} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 9) := by
  change certificateSparseVector (certificateDescendantColumns1 69) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 9)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 70. -/
theorem certificateDescendantColumn1_70_generated_step :
    certificateSparseVector (certificateDescendantColumns1 70) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 9) := by
  change certificateSparseVector (certificateDescendantColumns1 70) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 9)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 71. -/
theorem certificateDescendantColumn1_71_generated_step :
    certificateSparseVector (certificateDescendantColumns1 71) =
      certificateLocalLowering {0, 1, 2} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 10) := by
  change certificateSparseVector (certificateDescendantColumns1 71) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 10)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

end ThreeCopyQutritWerner
