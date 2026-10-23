module

public import ThreeCopyQutritWerner.CertificateDescendantData1

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped Matrix

namespace ThreeCopyQutritWerner

/-- Literal physical source binding for descendant column 168. -/
theorem certificateDescendantColumn1_168_generated_step :
    certificateSparseVector (certificateDescendantColumns1 168) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 73) := by
  change certificateSparseVector (certificateDescendantColumns1 168) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 73)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 169. -/
theorem certificateDescendantColumn1_169_generated_step :
    certificateSparseVector (certificateDescendantColumns1 169) =
      certificateLocalLowering {0, 1, 2} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 74) := by
  change certificateSparseVector (certificateDescendantColumns1 169) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 74)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 170. -/
theorem certificateDescendantColumn1_170_generated_step :
    certificateSparseVector (certificateDescendantColumns1 170) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 74) := by
  change certificateSparseVector (certificateDescendantColumns1 170) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 74)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 171. -/
theorem certificateDescendantColumn1_171_generated_step :
    certificateSparseVector (certificateDescendantColumns1 171) =
      certificateLocalLowering {0, 1, 2} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 75) := by
  change certificateSparseVector (certificateDescendantColumns1 171) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 75)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 172. -/
theorem certificateDescendantColumn1_172_generated_step :
    certificateSparseVector (certificateDescendantColumns1 172) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 75) := by
  change certificateSparseVector (certificateDescendantColumns1 172) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 75)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 173. -/
theorem certificateDescendantColumn1_173_generated_step :
    certificateSparseVector (certificateDescendantColumns1 173) =
      certificateLocalLowering {0, 1, 2} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 76) := by
  change certificateSparseVector (certificateDescendantColumns1 173) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 76)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 174. -/
theorem certificateDescendantColumn1_174_generated_step :
    certificateSparseVector (certificateDescendantColumns1 174) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 76) := by
  change certificateSparseVector (certificateDescendantColumns1 174) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 76)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 175. -/
theorem certificateDescendantColumn1_175_generated_step :
    certificateSparseVector (certificateDescendantColumns1 175) =
      certificateLocalLowering {0, 1, 2} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 77) := by
  change certificateSparseVector (certificateDescendantColumns1 175) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 77)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 176. -/
theorem certificateDescendantColumn1_176_generated_step :
    certificateSparseVector (certificateDescendantColumns1 176) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 77) := by
  change certificateSparseVector (certificateDescendantColumns1 176) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 77)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 177. -/
theorem certificateDescendantColumn1_177_generated_step :
    certificateSparseVector (certificateDescendantColumns1 177) =
      certificateLocalLowering {0, 1, 2} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 78) := by
  change certificateSparseVector (certificateDescendantColumns1 177) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 78)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 178. -/
theorem certificateDescendantColumn1_178_generated_step :
    certificateSparseVector (certificateDescendantColumns1 178) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 78) := by
  change certificateSparseVector (certificateDescendantColumns1 178) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 78)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 179. -/
theorem certificateDescendantColumn1_179_generated_step :
    certificateSparseVector (certificateDescendantColumns1 179) =
      certificateLocalLowering {0, 1, 2} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 79) := by
  change certificateSparseVector (certificateDescendantColumns1 179) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 79)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 180. -/
theorem certificateDescendantColumn1_180_generated_step :
    certificateSparseVector (certificateDescendantColumns1 180) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 79) := by
  change certificateSparseVector (certificateDescendantColumns1 180) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 79)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 181. -/
theorem certificateDescendantColumn1_181_generated_step :
    certificateSparseVector (certificateDescendantColumns1 181) =
      certificateLocalLowering {0, 1, 2} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 80) := by
  change certificateSparseVector (certificateDescendantColumns1 181) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 80)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 182. -/
theorem certificateDescendantColumn1_182_generated_step :
    certificateSparseVector (certificateDescendantColumns1 182) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 80) := by
  change certificateSparseVector (certificateDescendantColumns1 182) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 80)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 183. -/
theorem certificateDescendantColumn1_183_generated_step :
    certificateSparseVector (certificateDescendantColumns1 183) =
      certificateLocalLowering {0, 1, 2} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 81) := by
  change certificateSparseVector (certificateDescendantColumns1 183) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 81)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 184. -/
theorem certificateDescendantColumn1_184_generated_step :
    certificateSparseVector (certificateDescendantColumns1 184) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 81) := by
  change certificateSparseVector (certificateDescendantColumns1 184) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 81)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 185. -/
theorem certificateDescendantColumn1_185_generated_step :
    certificateSparseVector (certificateDescendantColumns1 185) =
      certificateLocalLowering {0, 1, 2} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 82) := by
  change certificateSparseVector (certificateDescendantColumns1 185) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 82)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 186. -/
theorem certificateDescendantColumn1_186_generated_step :
    certificateSparseVector (certificateDescendantColumns1 186) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 82) := by
  change certificateSparseVector (certificateDescendantColumns1 186) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 82)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 187. -/
theorem certificateDescendantColumn1_187_generated_step :
    certificateSparseVector (certificateDescendantColumns1 187) =
      certificateLocalLowering {0, 1, 2} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 83) := by
  change certificateSparseVector (certificateDescendantColumns1 187) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 83)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 188. -/
theorem certificateDescendantColumn1_188_generated_step :
    certificateSparseVector (certificateDescendantColumns1 188) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 83) := by
  change certificateSparseVector (certificateDescendantColumns1 188) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 83)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 189. -/
theorem certificateDescendantColumn1_189_generated_step :
    certificateSparseVector (certificateDescendantColumns1 189) =
      certificateLocalLowering {0, 1, 2} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 84) := by
  change certificateSparseVector (certificateDescendantColumns1 189) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 84)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 190. -/
theorem certificateDescendantColumn1_190_generated_step :
    certificateSparseVector (certificateDescendantColumns1 190) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 84) := by
  change certificateSparseVector (certificateDescendantColumns1 190) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 84)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 191. -/
theorem certificateDescendantColumn1_191_generated_step :
    certificateSparseVector (certificateDescendantColumns1 191) =
      certificateLocalLowering {0, 1, 2} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 85) := by
  change certificateSparseVector (certificateDescendantColumns1 191) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 85)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

end ThreeCopyQutritWerner
