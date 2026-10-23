module

public import ThreeCopyQutritWerner.LocalFramesForallPilot

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
open scoped Matrix
namespace ThreeCopyQutritWerner

/-- The exact archive metric in sector 1, local type 6, with its physical embedding. -/
theorem certificateLocalGram1_6_correct :
    (certificateLocalFrame1_6)ᵀ * certificateLocalFrame1_6 = certificateLocalGram1_6 := by
  exact certificateLocalGram1_6_forallPilot

end ThreeCopyQutritWerner
