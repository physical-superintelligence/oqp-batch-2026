module

public import ThreeCopyQutritWerner.CertificateDescendantData1

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped Matrix

namespace ThreeCopyQutritWerner

/-- Literal physical source binding for descendant column 360. -/
theorem certificateDescendantColumn1_360_generated_step :
    certificateSparseVector (certificateDescendantColumns1 360) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 239) := by
  change certificateSparseVector (certificateDescendantColumns1 360) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 239)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 361. -/
theorem certificateDescendantColumn1_361_generated_step :
    certificateSparseVector (certificateDescendantColumns1 361) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 241) := by
  change certificateSparseVector (certificateDescendantColumns1 361) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 241)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 362. -/
theorem certificateDescendantColumn1_362_generated_step :
    certificateSparseVector (certificateDescendantColumns1 362) =
      certificateLocalLowering {0, 1, 2} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 242) := by
  change certificateSparseVector (certificateDescendantColumns1 362) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 242)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 363. -/
theorem certificateDescendantColumn1_363_generated_step :
    certificateSparseVector (certificateDescendantColumns1 363) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 242) := by
  change certificateSparseVector (certificateDescendantColumns1 363) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 242)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 364. -/
theorem certificateDescendantColumn1_364_generated_step :
    certificateSparseVector (certificateDescendantColumns1 364) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 243) := by
  change certificateSparseVector (certificateDescendantColumns1 364) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 243)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 365. -/
theorem certificateDescendantColumn1_365_generated_step :
    certificateSparseVector (certificateDescendantColumns1 365) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 244) := by
  change certificateSparseVector (certificateDescendantColumns1 365) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 244)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 366. -/
theorem certificateDescendantColumn1_366_generated_step :
    certificateSparseVector (certificateDescendantColumns1 366) =
      certificateLocalLowering {0, 1, 2} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 245) := by
  change certificateSparseVector (certificateDescendantColumns1 366) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 245)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 367. -/
theorem certificateDescendantColumn1_367_generated_step :
    certificateSparseVector (certificateDescendantColumns1 367) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 245) := by
  change certificateSparseVector (certificateDescendantColumns1 367) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 245)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 368. -/
theorem certificateDescendantColumn1_368_generated_step :
    certificateSparseVector (certificateDescendantColumns1 368) =
      certificateLocalLowering {0, 1, 2} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 247) := by
  change certificateSparseVector (certificateDescendantColumns1 368) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 247)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 369. -/
theorem certificateDescendantColumn1_369_generated_step :
    certificateSparseVector (certificateDescendantColumns1 369) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 247) := by
  change certificateSparseVector (certificateDescendantColumns1 369) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 247)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 370. -/
theorem certificateDescendantColumn1_370_generated_step :
    certificateSparseVector (certificateDescendantColumns1 370) =
      certificateLocalLowering {0, 1, 2} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 248) := by
  change certificateSparseVector (certificateDescendantColumns1 370) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 248)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 371. -/
theorem certificateDescendantColumn1_371_generated_step :
    certificateSparseVector (certificateDescendantColumns1 371) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 248) := by
  change certificateSparseVector (certificateDescendantColumns1 371) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 248)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 372. -/
theorem certificateDescendantColumn1_372_generated_step :
    certificateSparseVector (certificateDescendantColumns1 372) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 249) := by
  change certificateSparseVector (certificateDescendantColumns1 372) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 249)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 373. -/
theorem certificateDescendantColumn1_373_generated_step :
    certificateSparseVector (certificateDescendantColumns1 373) =
      certificateLocalLowering {0, 1, 2} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 251) := by
  change certificateSparseVector (certificateDescendantColumns1 373) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 251)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 374. -/
theorem certificateDescendantColumn1_374_generated_step :
    certificateSparseVector (certificateDescendantColumns1 374) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 251) := by
  change certificateSparseVector (certificateDescendantColumns1 374) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 251)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 375. -/
theorem certificateDescendantColumn1_375_generated_step :
    certificateSparseVector (certificateDescendantColumns1 375) =
      certificateLocalLowering {0, 1, 2} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 252) := by
  change certificateSparseVector (certificateDescendantColumns1 375) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 252)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 376. -/
theorem certificateDescendantColumn1_376_generated_step :
    certificateSparseVector (certificateDescendantColumns1 376) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 252) := by
  change certificateSparseVector (certificateDescendantColumns1 376) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 252)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 377. -/
theorem certificateDescendantColumn1_377_generated_step :
    certificateSparseVector (certificateDescendantColumns1 377) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 253) := by
  change certificateSparseVector (certificateDescendantColumns1 377) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 253)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 378. -/
theorem certificateDescendantColumn1_378_generated_step :
    certificateSparseVector (certificateDescendantColumns1 378) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 255) := by
  change certificateSparseVector (certificateDescendantColumns1 378) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 255)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 379. -/
theorem certificateDescendantColumn1_379_generated_step :
    certificateSparseVector (certificateDescendantColumns1 379) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 256) := by
  change certificateSparseVector (certificateDescendantColumns1 379) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 256)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 380. -/
theorem certificateDescendantColumn1_380_generated_step :
    certificateSparseVector (certificateDescendantColumns1 380) =
      certificateLocalLowering {0, 1, 2} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 257) := by
  change certificateSparseVector (certificateDescendantColumns1 380) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 257)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 381. -/
theorem certificateDescendantColumn1_381_generated_step :
    certificateSparseVector (certificateDescendantColumns1 381) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 257) := by
  change certificateSparseVector (certificateDescendantColumns1 381) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 257)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 382. -/
theorem certificateDescendantColumn1_382_generated_step :
    certificateSparseVector (certificateDescendantColumns1 382) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 258) := by
  change certificateSparseVector (certificateDescendantColumns1 382) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 258)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 383. -/
theorem certificateDescendantColumn1_383_generated_step :
    certificateSparseVector (certificateDescendantColumns1 383) =
      certificateLocalLowering {0, 1, 2} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns1 259) := by
  change certificateSparseVector (certificateDescendantColumns1 383) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0, 1, 2} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns1 259)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

end ThreeCopyQutritWerner
