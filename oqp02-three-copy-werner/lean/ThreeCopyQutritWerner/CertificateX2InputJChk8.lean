module

public import ThreeCopyQutritWerner.CertificateX2InputJSym

@[expose] public section


/-! Kernel checks of the images' sign laws, part 8. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThreeCopyQutritWerner.X2

theorem x2JC_1_124_224_1 : x2JColRangeOK 1 ⟨124, by decide⟩ 224 1 = true := by
  decide +kernel

theorem x2JC_1_124_64_32 : x2JColRangeOK 1 ⟨124, by decide⟩ 64 32 = true := by
  decide +kernel

theorem x2JC_1_125_196_12 : x2JColRangeOK 1 ⟨125, by decide⟩ 196 12 = true := by
  decide +kernel

theorem x2JC_1_125_84_28 : x2JColRangeOK 1 ⟨125, by decide⟩ 84 28 = true := by
  decide +kernel

theorem x2JC_1_159_143_13 : x2JColRangeOK 1 ⟨159, by decide⟩ 143 13 = true := by
  decide +kernel

theorem x2JC_1_159_39_13 : x2JColRangeOK 1 ⟨159, by decide⟩ 39 13 = true := by
  decide +kernel

theorem x2JC_2_102_20_10 : x2JColRangeOK 2 ⟨102, by decide⟩ 20 10 = true := by
  decide +kernel

theorem x2JC_2_106_0_88 : x2JColRangeOK 2 ⟨106, by decide⟩ 0 88 = true := by
  decide +kernel

theorem x2JR_1_0_70 : x2JKeyRangeOK 1 0 70 = true := by
  decide +kernel

theorem x2JR_2_103_1 : x2JKeyRangeOK 2 103 1 = true := by
  decide +kernel

theorem x2JR_2_118_1 : x2JKeyRangeOK 2 118 1 = true := by
  decide +kernel

theorem x2JR_2_120_3 : x2JKeyRangeOK 2 120 3 = true := by
  decide +kernel

end ThreeCopyQutritWerner.X2
