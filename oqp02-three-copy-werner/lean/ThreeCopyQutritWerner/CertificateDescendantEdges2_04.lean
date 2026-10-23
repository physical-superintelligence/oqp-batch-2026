module

public import ThreeCopyQutritWerner.CertificateDescendantData

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped Matrix

namespace ThreeCopyQutritWerner

/-- Literal physical source binding for descendant column 96. -/
theorem certificateDescendantColumn2_96_generated_step :
    certificateSparseVector (certificateDescendantColumns2 96) =
      certificateLocalLowering {0} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 25) := by
  change certificateSparseVector (certificateDescendantColumns2 96) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 25)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 97. -/
theorem certificateDescendantColumn2_97_generated_step :
    certificateSparseVector (certificateDescendantColumns2 97) =
      certificateLocalLowering {0} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 25) := by
  change certificateSparseVector (certificateDescendantColumns2 97) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 25)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 98. -/
theorem certificateDescendantColumn2_98_generated_step :
    certificateSparseVector (certificateDescendantColumns2 98) =
      certificateLocalLowering {0} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 26) := by
  change certificateSparseVector (certificateDescendantColumns2 98) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 26)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 99. -/
theorem certificateDescendantColumn2_99_generated_step :
    certificateSparseVector (certificateDescendantColumns2 99) =
      certificateLocalLowering {0} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 26) := by
  change certificateSparseVector (certificateDescendantColumns2 99) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 26)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 100. -/
theorem certificateDescendantColumn2_100_generated_step :
    certificateSparseVector (certificateDescendantColumns2 100) =
      certificateLocalLowering {0} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 27) := by
  change certificateSparseVector (certificateDescendantColumns2 100) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 27)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 101. -/
theorem certificateDescendantColumn2_101_generated_step :
    certificateSparseVector (certificateDescendantColumns2 101) =
      certificateLocalLowering {0} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 27) := by
  change certificateSparseVector (certificateDescendantColumns2 101) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 27)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 102. -/
theorem certificateDescendantColumn2_102_generated_step :
    certificateSparseVector (certificateDescendantColumns2 102) =
      certificateLocalLowering {0} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 28) := by
  change certificateSparseVector (certificateDescendantColumns2 102) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 28)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 103. -/
theorem certificateDescendantColumn2_103_generated_step :
    certificateSparseVector (certificateDescendantColumns2 103) =
      certificateLocalLowering {0} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 28) := by
  change certificateSparseVector (certificateDescendantColumns2 103) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 28)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 104. -/
theorem certificateDescendantColumn2_104_generated_step :
    certificateSparseVector (certificateDescendantColumns2 104) =
      certificateLocalLowering {0} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 29) := by
  change certificateSparseVector (certificateDescendantColumns2 104) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 29)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 105. -/
theorem certificateDescendantColumn2_105_generated_step :
    certificateSparseVector (certificateDescendantColumns2 105) =
      certificateLocalLowering {0} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 29) := by
  change certificateSparseVector (certificateDescendantColumns2 105) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 29)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 106. -/
theorem certificateDescendantColumn2_106_generated_step :
    certificateSparseVector (certificateDescendantColumns2 106) =
      certificateLocalLowering {0} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 30) := by
  change certificateSparseVector (certificateDescendantColumns2 106) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 30)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 107. -/
theorem certificateDescendantColumn2_107_generated_step :
    certificateSparseVector (certificateDescendantColumns2 107) =
      certificateLocalLowering {0} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 31) := by
  change certificateSparseVector (certificateDescendantColumns2 107) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 31)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 108. -/
theorem certificateDescendantColumn2_108_generated_step :
    certificateSparseVector (certificateDescendantColumns2 108) =
      certificateLocalLowering {0} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 32) := by
  change certificateSparseVector (certificateDescendantColumns2 108) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 32)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 109. -/
theorem certificateDescendantColumn2_109_generated_step :
    certificateSparseVector (certificateDescendantColumns2 109) =
      certificateLocalLowering {0} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 33) := by
  change certificateSparseVector (certificateDescendantColumns2 109) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 33)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 110. -/
theorem certificateDescendantColumn2_110_generated_step :
    certificateSparseVector (certificateDescendantColumns2 110) =
      certificateLocalLowering {0} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 34) := by
  change certificateSparseVector (certificateDescendantColumns2 110) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 34)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 111. -/
theorem certificateDescendantColumn2_111_generated_step :
    certificateSparseVector (certificateDescendantColumns2 111) =
      certificateLocalLowering {0} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 35) := by
  change certificateSparseVector (certificateDescendantColumns2 111) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 35)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 112. -/
theorem certificateDescendantColumn2_112_generated_step :
    certificateSparseVector (certificateDescendantColumns2 112) =
      certificateLocalLowering {0} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 36) := by
  change certificateSparseVector (certificateDescendantColumns2 112) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 36)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 113. -/
theorem certificateDescendantColumn2_113_generated_step :
    certificateSparseVector (certificateDescendantColumns2 113) =
      certificateLocalLowering {0} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 37) := by
  change certificateSparseVector (certificateDescendantColumns2 113) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 37)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 114. -/
theorem certificateDescendantColumn2_114_generated_step :
    certificateSparseVector (certificateDescendantColumns2 114) =
      certificateLocalLowering {0} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 38) := by
  change certificateSparseVector (certificateDescendantColumns2 114) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 38)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 115. -/
theorem certificateDescendantColumn2_115_generated_step :
    certificateSparseVector (certificateDescendantColumns2 115) =
      certificateLocalLowering {0} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 39) := by
  change certificateSparseVector (certificateDescendantColumns2 115) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 39)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 116. -/
theorem certificateDescendantColumn2_116_generated_step :
    certificateSparseVector (certificateDescendantColumns2 116) =
      certificateLocalLowering {0} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 40) := by
  change certificateSparseVector (certificateDescendantColumns2 116) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 40)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 117. -/
theorem certificateDescendantColumn2_117_generated_step :
    certificateSparseVector (certificateDescendantColumns2 117) =
      certificateLocalLowering {0} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 41) := by
  change certificateSparseVector (certificateDescendantColumns2 117) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 41)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 118. -/
theorem certificateDescendantColumn2_118_generated_step :
    certificateSparseVector (certificateDescendantColumns2 118) =
      certificateLocalLowering {0} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 42) := by
  change certificateSparseVector (certificateDescendantColumns2 118) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 42)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 119. -/
theorem certificateDescendantColumn2_119_generated_step :
    certificateSparseVector (certificateDescendantColumns2 119) =
      certificateLocalLowering {0} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 43) := by
  change certificateSparseVector (certificateDescendantColumns2 119) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 43)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

end ThreeCopyQutritWerner
