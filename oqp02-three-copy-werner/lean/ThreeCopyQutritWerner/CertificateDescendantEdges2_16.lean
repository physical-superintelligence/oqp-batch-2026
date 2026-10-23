module

public import ThreeCopyQutritWerner.CertificateDescendantData

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped Matrix

namespace ThreeCopyQutritWerner

/-- Literal physical source binding for descendant column 384. -/
theorem certificateDescendantColumn2_384_generated_step :
    certificateSparseVector (certificateDescendantColumns2 384) =
      certificateLocalLowering {0} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 269) := by
  change certificateSparseVector (certificateDescendantColumns2 384) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 269)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 385. -/
theorem certificateDescendantColumn2_385_generated_step :
    certificateSparseVector (certificateDescendantColumns2 385) =
      certificateLocalLowering {0} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 271) := by
  change certificateSparseVector (certificateDescendantColumns2 385) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 271)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 386. -/
theorem certificateDescendantColumn2_386_generated_step :
    certificateSparseVector (certificateDescendantColumns2 386) =
      certificateLocalLowering {0} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 271) := by
  change certificateSparseVector (certificateDescendantColumns2 386) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 271)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 387. -/
theorem certificateDescendantColumn2_387_generated_step :
    certificateSparseVector (certificateDescendantColumns2 387) =
      certificateLocalLowering {0} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 272) := by
  change certificateSparseVector (certificateDescendantColumns2 387) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 272)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 388. -/
theorem certificateDescendantColumn2_388_generated_step :
    certificateSparseVector (certificateDescendantColumns2 388) =
      certificateLocalLowering {0} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 273) := by
  change certificateSparseVector (certificateDescendantColumns2 388) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 273)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 389. -/
theorem certificateDescendantColumn2_389_generated_step :
    certificateSparseVector (certificateDescendantColumns2 389) =
      certificateLocalLowering {0} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 273) := by
  change certificateSparseVector (certificateDescendantColumns2 389) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 273)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 390. -/
theorem certificateDescendantColumn2_390_generated_step :
    certificateSparseVector (certificateDescendantColumns2 390) =
      certificateLocalLowering {0} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 274) := by
  change certificateSparseVector (certificateDescendantColumns2 390) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 274)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 391. -/
theorem certificateDescendantColumn2_391_generated_step :
    certificateSparseVector (certificateDescendantColumns2 391) =
      certificateLocalLowering {0} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 275) := by
  change certificateSparseVector (certificateDescendantColumns2 391) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 275)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 392. -/
theorem certificateDescendantColumn2_392_generated_step :
    certificateSparseVector (certificateDescendantColumns2 392) =
      certificateLocalLowering {0} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 275) := by
  change certificateSparseVector (certificateDescendantColumns2 392) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 275)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 393. -/
theorem certificateDescendantColumn2_393_generated_step :
    certificateSparseVector (certificateDescendantColumns2 393) =
      certificateLocalLowering {0} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 276) := by
  change certificateSparseVector (certificateDescendantColumns2 393) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 276)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 394. -/
theorem certificateDescendantColumn2_394_generated_step :
    certificateSparseVector (certificateDescendantColumns2 394) =
      certificateLocalLowering {0} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 277) := by
  change certificateSparseVector (certificateDescendantColumns2 394) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 277)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 395. -/
theorem certificateDescendantColumn2_395_generated_step :
    certificateSparseVector (certificateDescendantColumns2 395) =
      certificateLocalLowering {0} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 277) := by
  change certificateSparseVector (certificateDescendantColumns2 395) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 277)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 396. -/
theorem certificateDescendantColumn2_396_generated_step :
    certificateSparseVector (certificateDescendantColumns2 396) =
      certificateLocalLowering {0} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 278) := by
  change certificateSparseVector (certificateDescendantColumns2 396) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 278)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 397. -/
theorem certificateDescendantColumn2_397_generated_step :
    certificateSparseVector (certificateDescendantColumns2 397) =
      certificateLocalLowering {0} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 279) := by
  change certificateSparseVector (certificateDescendantColumns2 397) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 279)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 398. -/
theorem certificateDescendantColumn2_398_generated_step :
    certificateSparseVector (certificateDescendantColumns2 398) =
      certificateLocalLowering {0} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 279) := by
  change certificateSparseVector (certificateDescendantColumns2 398) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 279)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 399. -/
theorem certificateDescendantColumn2_399_generated_step :
    certificateSparseVector (certificateDescendantColumns2 399) =
      certificateLocalLowering {0} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 280) := by
  change certificateSparseVector (certificateDescendantColumns2 399) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 280)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 400. -/
theorem certificateDescendantColumn2_400_generated_step :
    certificateSparseVector (certificateDescendantColumns2 400) =
      certificateLocalLowering {0} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 281) := by
  change certificateSparseVector (certificateDescendantColumns2 400) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 281)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 401. -/
theorem certificateDescendantColumn2_401_generated_step :
    certificateSparseVector (certificateDescendantColumns2 401) =
      certificateLocalLowering {0} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 282) := by
  change certificateSparseVector (certificateDescendantColumns2 401) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 282)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 402. -/
theorem certificateDescendantColumn2_402_generated_step :
    certificateSparseVector (certificateDescendantColumns2 402) =
      certificateLocalLowering {0} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 282) := by
  change certificateSparseVector (certificateDescendantColumns2 402) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 282)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 403. -/
theorem certificateDescendantColumn2_403_generated_step :
    certificateSparseVector (certificateDescendantColumns2 403) =
      certificateLocalLowering {0} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 283) := by
  change certificateSparseVector (certificateDescendantColumns2 403) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 283)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 404. -/
theorem certificateDescendantColumn2_404_generated_step :
    certificateSparseVector (certificateDescendantColumns2 404) =
      certificateLocalLowering {0} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 285) := by
  change certificateSparseVector (certificateDescendantColumns2 404) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 285)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 405. -/
theorem certificateDescendantColumn2_405_generated_step :
    certificateSparseVector (certificateDescendantColumns2 405) =
      certificateLocalLowering {0} 0 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 286) := by
  change certificateSparseVector (certificateDescendantColumns2 405) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 1 0 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 286)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 406. -/
theorem certificateDescendantColumn2_406_generated_step :
    certificateSparseVector (certificateDescendantColumns2 406) =
      certificateLocalLowering {0} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 286) := by
  change certificateSparseVector (certificateDescendantColumns2 406) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 286)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

/-- Literal physical source binding for descendant column 407. -/
theorem certificateDescendantColumn2_407_generated_step :
    certificateSparseVector (certificateDescendantColumns2 407) =
      certificateLocalLowering {0} 1 *ᵥ
        certificateSparseVector (certificateDescendantColumns2 287) := by
  change certificateSparseVector (certificateDescendantColumns2 407) =
    (fun r c => certificateSparseVector (certificateLocalGeneratorWord {0} 2 1 c) r) *ᵥ
      certificateSparseVector (certificateDescendantColumns2 287)
  rw [certificateSparseAction_eq_mulVec]
  apply certificateSparseVector_eq_of_support
  decide

end ThreeCopyQutritWerner
