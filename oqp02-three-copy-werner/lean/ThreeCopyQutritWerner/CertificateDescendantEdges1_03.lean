module

public import ThreeCopyQutritWerner.CertificateDescendantData1

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped Matrix

namespace ThreeCopyQutritWerner

/-- Literal physical source binding for descendant column 72. -/
theorem certificateDescendantColumn1_72_generated_step :
    certificateSparseVector (certificateDescendantColumns1 72) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 10) := by
  change certificateSparseVector (certificateDescendantColumns1 72) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 10)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 73. -/
theorem certificateDescendantColumn1_73_generated_step :
    certificateSparseVector (certificateDescendantColumns1 73) =
      certificateLocalLowering {0, 1, 2} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 11) := by
  change certificateSparseVector (certificateDescendantColumns1 73) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 11)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 74. -/
theorem certificateDescendantColumn1_74_generated_step :
    certificateSparseVector (certificateDescendantColumns1 74) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 11) := by
  change certificateSparseVector (certificateDescendantColumns1 74) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 11)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 75. -/
theorem certificateDescendantColumn1_75_generated_step :
    certificateSparseVector (certificateDescendantColumns1 75) =
      certificateLocalLowering {0, 1, 2} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 12) := by
  change certificateSparseVector (certificateDescendantColumns1 75) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 12)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 76. -/
theorem certificateDescendantColumn1_76_generated_step :
    certificateSparseVector (certificateDescendantColumns1 76) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 12) := by
  change certificateSparseVector (certificateDescendantColumns1 76) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 12)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 77. -/
theorem certificateDescendantColumn1_77_generated_step :
    certificateSparseVector (certificateDescendantColumns1 77) =
      certificateLocalLowering {0, 1, 2} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 13) := by
  change certificateSparseVector (certificateDescendantColumns1 77) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 13)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 78. -/
theorem certificateDescendantColumn1_78_generated_step :
    certificateSparseVector (certificateDescendantColumns1 78) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 13) := by
  change certificateSparseVector (certificateDescendantColumns1 78) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 13)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 79. -/
theorem certificateDescendantColumn1_79_generated_step :
    certificateSparseVector (certificateDescendantColumns1 79) =
      certificateLocalLowering {0, 1, 2} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 14) := by
  change certificateSparseVector (certificateDescendantColumns1 79) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 14)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 80. -/
theorem certificateDescendantColumn1_80_generated_step :
    certificateSparseVector (certificateDescendantColumns1 80) =
      certificateLocalLowering {0, 1, 2} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 15) := by
  change certificateSparseVector (certificateDescendantColumns1 80) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 15)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 81. -/
theorem certificateDescendantColumn1_81_generated_step :
    certificateSparseVector (certificateDescendantColumns1 81) =
      certificateLocalLowering {0, 1, 2} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 16) := by
  change certificateSparseVector (certificateDescendantColumns1 81) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 16)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 82. -/
theorem certificateDescendantColumn1_82_generated_step :
    certificateSparseVector (certificateDescendantColumns1 82) =
      certificateLocalLowering {0, 1, 2} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 17) := by
  change certificateSparseVector (certificateDescendantColumns1 82) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 17)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 83. -/
theorem certificateDescendantColumn1_83_generated_step :
    certificateSparseVector (certificateDescendantColumns1 83) =
      certificateLocalLowering {0, 1, 2} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 18) := by
  change certificateSparseVector (certificateDescendantColumns1 83) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 18)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 84. -/
theorem certificateDescendantColumn1_84_generated_step :
    certificateSparseVector (certificateDescendantColumns1 84) =
      certificateLocalLowering {0, 1, 2} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 19) := by
  change certificateSparseVector (certificateDescendantColumns1 84) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 19)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 85. -/
theorem certificateDescendantColumn1_85_generated_step :
    certificateSparseVector (certificateDescendantColumns1 85) =
      certificateLocalLowering {0, 1, 2} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 20) := by
  change certificateSparseVector (certificateDescendantColumns1 85) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 20)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 86. -/
theorem certificateDescendantColumn1_86_generated_step :
    certificateSparseVector (certificateDescendantColumns1 86) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 21) := by
  change certificateSparseVector (certificateDescendantColumns1 86) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 21)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 87. -/
theorem certificateDescendantColumn1_87_generated_step :
    certificateSparseVector (certificateDescendantColumns1 87) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 22) := by
  change certificateSparseVector (certificateDescendantColumns1 87) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 22)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 88. -/
theorem certificateDescendantColumn1_88_generated_step :
    certificateSparseVector (certificateDescendantColumns1 88) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 23) := by
  change certificateSparseVector (certificateDescendantColumns1 88) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 23)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 89. -/
theorem certificateDescendantColumn1_89_generated_step :
    certificateSparseVector (certificateDescendantColumns1 89) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 24) := by
  change certificateSparseVector (certificateDescendantColumns1 89) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 24)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 90. -/
theorem certificateDescendantColumn1_90_generated_step :
    certificateSparseVector (certificateDescendantColumns1 90) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 25) := by
  change certificateSparseVector (certificateDescendantColumns1 90) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 25)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 91. -/
theorem certificateDescendantColumn1_91_generated_step :
    certificateSparseVector (certificateDescendantColumns1 91) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 26) := by
  change certificateSparseVector (certificateDescendantColumns1 91) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 26)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 92. -/
theorem certificateDescendantColumn1_92_generated_step :
    certificateSparseVector (certificateDescendantColumns1 92) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 27) := by
  change certificateSparseVector (certificateDescendantColumns1 92) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 27)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 93. -/
theorem certificateDescendantColumn1_93_generated_step :
    certificateSparseVector (certificateDescendantColumns1 93) =
      certificateLocalLowering {0, 1, 2} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 28) := by
  change certificateSparseVector (certificateDescendantColumns1 93) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 28)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 94. -/
theorem certificateDescendantColumn1_94_generated_step :
    certificateSparseVector (certificateDescendantColumns1 94) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 28) := by
  change certificateSparseVector (certificateDescendantColumns1 94) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 28)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 95. -/
theorem certificateDescendantColumn1_95_generated_step :
    certificateSparseVector (certificateDescendantColumns1 95) =
      certificateLocalLowering {0, 1, 2} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 29) := by
  change certificateSparseVector (certificateDescendantColumns1 95) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 29)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

end ThreeCopyQutritWerner
