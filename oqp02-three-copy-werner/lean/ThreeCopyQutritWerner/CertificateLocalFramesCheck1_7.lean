module

public import ThreeCopyQutritWerner.LocalFramesForallPilot

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
open scoped Matrix
namespace ThreeCopyQutritWerner

/-- The exact archive metric in sector 1, local type 7, with its physical embedding. -/
theorem certificateLocalGram1_7_correct :
    (certificateLocalFrame1_7)ᵀ * certificateLocalFrame1_7 = certificateLocalGram1_7 := by
  exact certificateLocalGram1_7_forallPilot

end ThreeCopyQutritWerner
