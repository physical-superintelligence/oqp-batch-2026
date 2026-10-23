module

public import ThreeCopyQutritWerner.CertificateDescendantData

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped Matrix

namespace ThreeCopyQutritWerner

/-- Literal physical source binding for descendant column 192. -/
theorem certificateDescendantColumn2_192_generated_step :
    certificateSparseVector (certificateDescendantColumns2 192) =
      certificateLocalLowering {0} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 90) := by
  change certificateSparseVector (certificateDescendantColumns2 192) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 90)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 193. -/
theorem certificateDescendantColumn2_193_generated_step :
    certificateSparseVector (certificateDescendantColumns2 193) =
      certificateLocalLowering {0} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 91) := by
  change certificateSparseVector (certificateDescendantColumns2 193) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 91)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 194. -/
theorem certificateDescendantColumn2_194_generated_step :
    certificateSparseVector (certificateDescendantColumns2 194) =
      certificateLocalLowering {0} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 91) := by
  change certificateSparseVector (certificateDescendantColumns2 194) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 91)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 195. -/
theorem certificateDescendantColumn2_195_generated_step :
    certificateSparseVector (certificateDescendantColumns2 195) =
      certificateLocalLowering {0} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 92) := by
  change certificateSparseVector (certificateDescendantColumns2 195) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 92)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 196. -/
theorem certificateDescendantColumn2_196_generated_step :
    certificateSparseVector (certificateDescendantColumns2 196) =
      certificateLocalLowering {0} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 93) := by
  change certificateSparseVector (certificateDescendantColumns2 196) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 93)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 197. -/
theorem certificateDescendantColumn2_197_generated_step :
    certificateSparseVector (certificateDescendantColumns2 197) =
      certificateLocalLowering {0} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 93) := by
  change certificateSparseVector (certificateDescendantColumns2 197) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 93)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 198. -/
theorem certificateDescendantColumn2_198_generated_step :
    certificateSparseVector (certificateDescendantColumns2 198) =
      certificateLocalLowering {0} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 94) := by
  change certificateSparseVector (certificateDescendantColumns2 198) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 94)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 199. -/
theorem certificateDescendantColumn2_199_generated_step :
    certificateSparseVector (certificateDescendantColumns2 199) =
      certificateLocalLowering {0} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 95) := by
  change certificateSparseVector (certificateDescendantColumns2 199) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 95)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 200. -/
theorem certificateDescendantColumn2_200_generated_step :
    certificateSparseVector (certificateDescendantColumns2 200) =
      certificateLocalLowering {0} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 95) := by
  change certificateSparseVector (certificateDescendantColumns2 200) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 95)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 201. -/
theorem certificateDescendantColumn2_201_generated_step :
    certificateSparseVector (certificateDescendantColumns2 201) =
      certificateLocalLowering {0} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 96) := by
  change certificateSparseVector (certificateDescendantColumns2 201) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 96)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 202. -/
theorem certificateDescendantColumn2_202_generated_step :
    certificateSparseVector (certificateDescendantColumns2 202) =
      certificateLocalLowering {0} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 97) := by
  change certificateSparseVector (certificateDescendantColumns2 202) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 97)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 203. -/
theorem certificateDescendantColumn2_203_generated_step :
    certificateSparseVector (certificateDescendantColumns2 203) =
      certificateLocalLowering {0} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 97) := by
  change certificateSparseVector (certificateDescendantColumns2 203) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 97)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 204. -/
theorem certificateDescendantColumn2_204_generated_step :
    certificateSparseVector (certificateDescendantColumns2 204) =
      certificateLocalLowering {0} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 98) := by
  change certificateSparseVector (certificateDescendantColumns2 204) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 98)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 205. -/
theorem certificateDescendantColumn2_205_generated_step :
    certificateSparseVector (certificateDescendantColumns2 205) =
      certificateLocalLowering {0} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 99) := by
  change certificateSparseVector (certificateDescendantColumns2 205) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 99)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 206. -/
theorem certificateDescendantColumn2_206_generated_step :
    certificateSparseVector (certificateDescendantColumns2 206) =
      certificateLocalLowering {0} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 99) := by
  change certificateSparseVector (certificateDescendantColumns2 206) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 99)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 207. -/
theorem certificateDescendantColumn2_207_generated_step :
    certificateSparseVector (certificateDescendantColumns2 207) =
      certificateLocalLowering {0} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 100) := by
  change certificateSparseVector (certificateDescendantColumns2 207) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 100)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 208. -/
theorem certificateDescendantColumn2_208_generated_step :
    certificateSparseVector (certificateDescendantColumns2 208) =
      certificateLocalLowering {0} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 101) := by
  change certificateSparseVector (certificateDescendantColumns2 208) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 101)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 209. -/
theorem certificateDescendantColumn2_209_generated_step :
    certificateSparseVector (certificateDescendantColumns2 209) =
      certificateLocalLowering {0} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 101) := by
  change certificateSparseVector (certificateDescendantColumns2 209) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 101)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 210. -/
theorem certificateDescendantColumn2_210_generated_step :
    certificateSparseVector (certificateDescendantColumns2 210) =
      certificateLocalLowering {0} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 102) := by
  change certificateSparseVector (certificateDescendantColumns2 210) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 102)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 211. -/
theorem certificateDescendantColumn2_211_generated_step :
    certificateSparseVector (certificateDescendantColumns2 211) =
      certificateLocalLowering {0} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 103) := by
  change certificateSparseVector (certificateDescendantColumns2 211) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 103)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 212. -/
theorem certificateDescendantColumn2_212_generated_step :
    certificateSparseVector (certificateDescendantColumns2 212) =
      certificateLocalLowering {0} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 103) := by
  change certificateSparseVector (certificateDescendantColumns2 212) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 103)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 213. -/
theorem certificateDescendantColumn2_213_generated_step :
    certificateSparseVector (certificateDescendantColumns2 213) =
      certificateLocalLowering {0} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 104) := by
  change certificateSparseVector (certificateDescendantColumns2 213) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 104)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 214. -/
theorem certificateDescendantColumn2_214_generated_step :
    certificateSparseVector (certificateDescendantColumns2 214) =
      certificateLocalLowering {0} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 105) := by
  change certificateSparseVector (certificateDescendantColumns2 214) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 105)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 215. -/
theorem certificateDescendantColumn2_215_generated_step :
    certificateSparseVector (certificateDescendantColumns2 215) =
      certificateLocalLowering {0} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 105) := by
  change certificateSparseVector (certificateDescendantColumns2 215) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 105)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

end ThreeCopyQutritWerner
