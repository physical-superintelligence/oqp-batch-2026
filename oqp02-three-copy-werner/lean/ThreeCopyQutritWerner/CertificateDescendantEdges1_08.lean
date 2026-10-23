module

public import ThreeCopyQutritWerner.CertificateDescendantData1

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped Matrix

namespace ThreeCopyQutritWerner

/-- Literal physical source binding for descendant column 192. -/
theorem certificateDescendantColumn1_192_generated_step :
    certificateSparseVector (certificateDescendantColumns1 192) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 85) := by
  change certificateSparseVector (certificateDescendantColumns1 192) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 85)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 193. -/
theorem certificateDescendantColumn1_193_generated_step :
    certificateSparseVector (certificateDescendantColumns1 193) =
      certificateLocalLowering {0, 1, 2} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 86) := by
  change certificateSparseVector (certificateDescendantColumns1 193) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 86)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 194. -/
theorem certificateDescendantColumn1_194_generated_step :
    certificateSparseVector (certificateDescendantColumns1 194) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 86) := by
  change certificateSparseVector (certificateDescendantColumns1 194) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 86)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 195. -/
theorem certificateDescendantColumn1_195_generated_step :
    certificateSparseVector (certificateDescendantColumns1 195) =
      certificateLocalLowering {0, 1, 2} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 87) := by
  change certificateSparseVector (certificateDescendantColumns1 195) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 87)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 196. -/
theorem certificateDescendantColumn1_196_generated_step :
    certificateSparseVector (certificateDescendantColumns1 196) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 87) := by
  change certificateSparseVector (certificateDescendantColumns1 196) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 87)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 197. -/
theorem certificateDescendantColumn1_197_generated_step :
    certificateSparseVector (certificateDescendantColumns1 197) =
      certificateLocalLowering {0, 1, 2} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 88) := by
  change certificateSparseVector (certificateDescendantColumns1 197) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 88)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 198. -/
theorem certificateDescendantColumn1_198_generated_step :
    certificateSparseVector (certificateDescendantColumns1 198) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 88) := by
  change certificateSparseVector (certificateDescendantColumns1 198) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 88)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 199. -/
theorem certificateDescendantColumn1_199_generated_step :
    certificateSparseVector (certificateDescendantColumns1 199) =
      certificateLocalLowering {0, 1, 2} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 89) := by
  change certificateSparseVector (certificateDescendantColumns1 199) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 89)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 200. -/
theorem certificateDescendantColumn1_200_generated_step :
    certificateSparseVector (certificateDescendantColumns1 200) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 89) := by
  change certificateSparseVector (certificateDescendantColumns1 200) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 89)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 201. -/
theorem certificateDescendantColumn1_201_generated_step :
    certificateSparseVector (certificateDescendantColumns1 201) =
      certificateLocalLowering {0, 1, 2} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 90) := by
  change certificateSparseVector (certificateDescendantColumns1 201) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 90)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 202. -/
theorem certificateDescendantColumn1_202_generated_step :
    certificateSparseVector (certificateDescendantColumns1 202) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 90) := by
  change certificateSparseVector (certificateDescendantColumns1 202) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 90)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 203. -/
theorem certificateDescendantColumn1_203_generated_step :
    certificateSparseVector (certificateDescendantColumns1 203) =
      certificateLocalLowering {0, 1, 2} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 91) := by
  change certificateSparseVector (certificateDescendantColumns1 203) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 91)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 204. -/
theorem certificateDescendantColumn1_204_generated_step :
    certificateSparseVector (certificateDescendantColumns1 204) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 91) := by
  change certificateSparseVector (certificateDescendantColumns1 204) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 91)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 205. -/
theorem certificateDescendantColumn1_205_generated_step :
    certificateSparseVector (certificateDescendantColumns1 205) =
      certificateLocalLowering {0, 1, 2} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 92) := by
  change certificateSparseVector (certificateDescendantColumns1 205) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 92)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 206. -/
theorem certificateDescendantColumn1_206_generated_step :
    certificateSparseVector (certificateDescendantColumns1 206) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 92) := by
  change certificateSparseVector (certificateDescendantColumns1 206) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 92)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 207. -/
theorem certificateDescendantColumn1_207_generated_step :
    certificateSparseVector (certificateDescendantColumns1 207) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 93) := by
  change certificateSparseVector (certificateDescendantColumns1 207) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 93)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 208. -/
theorem certificateDescendantColumn1_208_generated_step :
    certificateSparseVector (certificateDescendantColumns1 208) =
      certificateLocalLowering {0, 1, 2} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 94) := by
  change certificateSparseVector (certificateDescendantColumns1 208) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 94)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 209. -/
theorem certificateDescendantColumn1_209_generated_step :
    certificateSparseVector (certificateDescendantColumns1 209) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 95) := by
  change certificateSparseVector (certificateDescendantColumns1 209) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 95)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 210. -/
theorem certificateDescendantColumn1_210_generated_step :
    certificateSparseVector (certificateDescendantColumns1 210) =
      certificateLocalLowering {0, 1, 2} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 96) := by
  change certificateSparseVector (certificateDescendantColumns1 210) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 96)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 211. -/
theorem certificateDescendantColumn1_211_generated_step :
    certificateSparseVector (certificateDescendantColumns1 211) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 97) := by
  change certificateSparseVector (certificateDescendantColumns1 211) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 97)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 212. -/
theorem certificateDescendantColumn1_212_generated_step :
    certificateSparseVector (certificateDescendantColumns1 212) =
      certificateLocalLowering {0, 1, 2} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 98) := by
  change certificateSparseVector (certificateDescendantColumns1 212) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 98)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 213. -/
theorem certificateDescendantColumn1_213_generated_step :
    certificateSparseVector (certificateDescendantColumns1 213) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 99) := by
  change certificateSparseVector (certificateDescendantColumns1 213) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 99)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 214. -/
theorem certificateDescendantColumn1_214_generated_step :
    certificateSparseVector (certificateDescendantColumns1 214) =
      certificateLocalLowering {0, 1, 2} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 100) := by
  change certificateSparseVector (certificateDescendantColumns1 214) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 100)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 215. -/
theorem certificateDescendantColumn1_215_generated_step :
    certificateSparseVector (certificateDescendantColumns1 215) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 101) := by
  change certificateSparseVector (certificateDescendantColumns1 215) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 101)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

end ThreeCopyQutritWerner
