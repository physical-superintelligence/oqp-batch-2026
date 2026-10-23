module

public import ThreeCopyQutritWerner.CertificateX2InputJSym

@[expose] public section


/-! Kernel checks of the images' sign laws, part 6. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThreeCopyQutritWerner.X2

theorem x2JC_1_124_0_32 : x2JColRangeOK 1 ⟨124, by decide⟩ 0 32 = true := by
  decide +kernel

theorem x2JC_1_124_192_32 : x2JColRangeOK 1 ⟨124, by decide⟩ 192 32 = true := by
  decide +kernel

theorem x2JC_1_142_164_16 : x2JColRangeOK 1 ⟨142, by decide⟩ 164 16 = true := by
  decide +kernel

theorem x2JC_1_143_0_36 : x2JColRangeOK 1 ⟨143, by decide⟩ 0 36 = true := by
  decide +kernel

theorem x2JC_1_155_36_36 : x2JColRangeOK 1 ⟨155, by decide⟩ 36 36 = true := by
  decide +kernel

theorem x2JC_1_160_28_7 : x2JColRangeOK 1 ⟨160, by decide⟩ 28 7 = true := by
  decide +kernel

theorem x2JC_1_160_84_7 : x2JColRangeOK 1 ⟨160, by decide⟩ 84 7 = true := by
  decide +kernel

theorem x2JC_1_163_82_41 : x2JColRangeOK 1 ⟨163, by decide⟩ 82 41 = true := by
  decide +kernel

theorem x2JC_2_102_30_8 : x2JColRangeOK 2 ⟨102, by decide⟩ 30 8 = true := by
  decide +kernel

theorem x2JC_2_104_88_16 : x2JColRangeOK 2 ⟨104, by decide⟩ 88 16 = true := by
  decide +kernel

theorem x2JR_2_67_9 : x2JKeyRangeOK 2 67 9 = true := by
  decide +kernel

end ThreeCopyQutritWerner.X2
