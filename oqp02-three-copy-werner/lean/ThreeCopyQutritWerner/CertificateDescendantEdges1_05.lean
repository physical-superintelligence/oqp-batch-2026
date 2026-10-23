module

public import ThreeCopyQutritWerner.CertificateDescendantData1

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped Matrix

namespace ThreeCopyQutritWerner

/-- Literal physical source binding for descendant column 120. -/
theorem certificateDescendantColumn1_120_generated_step :
    certificateSparseVector (certificateDescendantColumns1 120) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 41) := by
  change certificateSparseVector (certificateDescendantColumns1 120) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 41)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 121. -/
theorem certificateDescendantColumn1_121_generated_step :
    certificateSparseVector (certificateDescendantColumns1 121) =
      certificateLocalLowering {0, 1, 2} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 42) := by
  change certificateSparseVector (certificateDescendantColumns1 121) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 42)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 122. -/
theorem certificateDescendantColumn1_122_generated_step :
    certificateSparseVector (certificateDescendantColumns1 122) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 42) := by
  change certificateSparseVector (certificateDescendantColumns1 122) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 42)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 123. -/
theorem certificateDescendantColumn1_123_generated_step :
    certificateSparseVector (certificateDescendantColumns1 123) =
      certificateLocalLowering {0, 1, 2} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 43) := by
  change certificateSparseVector (certificateDescendantColumns1 123) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 43)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 124. -/
theorem certificateDescendantColumn1_124_generated_step :
    certificateSparseVector (certificateDescendantColumns1 124) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 43) := by
  change certificateSparseVector (certificateDescendantColumns1 124) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 43)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 125. -/
theorem certificateDescendantColumn1_125_generated_step :
    certificateSparseVector (certificateDescendantColumns1 125) =
      certificateLocalLowering {0, 1, 2} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 44) := by
  change certificateSparseVector (certificateDescendantColumns1 125) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 44)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 126. -/
theorem certificateDescendantColumn1_126_generated_step :
    certificateSparseVector (certificateDescendantColumns1 126) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 44) := by
  change certificateSparseVector (certificateDescendantColumns1 126) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 44)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 127. -/
theorem certificateDescendantColumn1_127_generated_step :
    certificateSparseVector (certificateDescendantColumns1 127) =
      certificateLocalLowering {0, 1, 2} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 51) := by
  change certificateSparseVector (certificateDescendantColumns1 127) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 51)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 128. -/
theorem certificateDescendantColumn1_128_generated_step :
    certificateSparseVector (certificateDescendantColumns1 128) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 51) := by
  change certificateSparseVector (certificateDescendantColumns1 128) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 51)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 129. -/
theorem certificateDescendantColumn1_129_generated_step :
    certificateSparseVector (certificateDescendantColumns1 129) =
      certificateLocalLowering {0, 1, 2} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 52) := by
  change certificateSparseVector (certificateDescendantColumns1 129) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 52)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 130. -/
theorem certificateDescendantColumn1_130_generated_step :
    certificateSparseVector (certificateDescendantColumns1 130) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 52) := by
  change certificateSparseVector (certificateDescendantColumns1 130) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 52)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 131. -/
theorem certificateDescendantColumn1_131_generated_step :
    certificateSparseVector (certificateDescendantColumns1 131) =
      certificateLocalLowering {0, 1, 2} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 53) := by
  change certificateSparseVector (certificateDescendantColumns1 131) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 53)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 132. -/
theorem certificateDescendantColumn1_132_generated_step :
    certificateSparseVector (certificateDescendantColumns1 132) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 53) := by
  change certificateSparseVector (certificateDescendantColumns1 132) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 53)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 133. -/
theorem certificateDescendantColumn1_133_generated_step :
    certificateSparseVector (certificateDescendantColumns1 133) =
      certificateLocalLowering {0, 1, 2} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 54) := by
  change certificateSparseVector (certificateDescendantColumns1 133) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 54)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 134. -/
theorem certificateDescendantColumn1_134_generated_step :
    certificateSparseVector (certificateDescendantColumns1 134) =
      certificateLocalLowering {0, 1, 2} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 55) := by
  change certificateSparseVector (certificateDescendantColumns1 134) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 55)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 135. -/
theorem certificateDescendantColumn1_135_generated_step :
    certificateSparseVector (certificateDescendantColumns1 135) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 55) := by
  change certificateSparseVector (certificateDescendantColumns1 135) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 55)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 136. -/
theorem certificateDescendantColumn1_136_generated_step :
    certificateSparseVector (certificateDescendantColumns1 136) =
      certificateLocalLowering {0, 1, 2} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 56) := by
  change certificateSparseVector (certificateDescendantColumns1 136) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 56)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 137. -/
theorem certificateDescendantColumn1_137_generated_step :
    certificateSparseVector (certificateDescendantColumns1 137) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 57) := by
  change certificateSparseVector (certificateDescendantColumns1 137) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 57)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 138. -/
theorem certificateDescendantColumn1_138_generated_step :
    certificateSparseVector (certificateDescendantColumns1 138) =
      certificateLocalLowering {0, 1, 2} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 58) := by
  change certificateSparseVector (certificateDescendantColumns1 138) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 58)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 139. -/
theorem certificateDescendantColumn1_139_generated_step :
    certificateSparseVector (certificateDescendantColumns1 139) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 58) := by
  change certificateSparseVector (certificateDescendantColumns1 139) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 58)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 140. -/
theorem certificateDescendantColumn1_140_generated_step :
    certificateSparseVector (certificateDescendantColumns1 140) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 59) := by
  change certificateSparseVector (certificateDescendantColumns1 140) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 59)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 141. -/
theorem certificateDescendantColumn1_141_generated_step :
    certificateSparseVector (certificateDescendantColumns1 141) =
      certificateLocalLowering {0, 1, 2} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 60) := by
  change certificateSparseVector (certificateDescendantColumns1 141) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 60)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 142. -/
theorem certificateDescendantColumn1_142_generated_step :
    certificateSparseVector (certificateDescendantColumns1 142) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 60) := by
  change certificateSparseVector (certificateDescendantColumns1 142) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 60)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 143. -/
theorem certificateDescendantColumn1_143_generated_step :
    certificateSparseVector (certificateDescendantColumns1 143) =
      certificateLocalLowering {0, 1, 2} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 61) := by
  change certificateSparseVector (certificateDescendantColumns1 143) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 61)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

end ThreeCopyQutritWerner
