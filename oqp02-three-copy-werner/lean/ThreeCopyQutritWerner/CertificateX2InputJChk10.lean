module

public import ThreeCopyQutritWerner.CertificateX2InputJSym

@[expose] public section


/-! Kernel checks of the images' sign laws, part 10. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThreeCopyQutritWerner.X2

theorem x2JC_1_124_128_32 : x2JColRangeOK 1 ⟨124, by decide⟩ 128 32 = true := by
  decide +kernel

theorem x2JC_1_125_168_28 : x2JColRangeOK 1 ⟨125, by decide⟩ 168 28 = true := by
  decide +kernel

theorem x2JC_1_142_41_41 : x2JColRangeOK 1 ⟨142, by decide⟩ 41 41 = true := by
  decide +kernel

theorem x2JC_1_143_144_13 : x2JColRangeOK 1 ⟨143, by decide⟩ 144 13 = true := by
  decide +kernel

theorem x2JC_1_159_156_3 : x2JColRangeOK 1 ⟨159, by decide⟩ 156 3 = true := by
  decide +kernel

theorem x2JC_1_159_78_13 : x2JColRangeOK 1 ⟨159, by decide⟩ 78 13 = true := by
  decide +kernel

theorem x2JC_1_160_56_7 : x2JColRangeOK 1 ⟨160, by decide⟩ 56 7 = true := by
  decide +kernel

theorem x2JC_1_160_7_7 : x2JColRangeOK 1 ⟨160, by decide⟩ 7 7 = true := by
  decide +kernel

theorem x2JC_2_105_32_32 : x2JColRangeOK 2 ⟨105, by decide⟩ 32 32 = true := by
  decide +kernel

theorem x2JR_2_117_1 : x2JKeyRangeOK 2 117 1 = true := by
  decide +kernel

theorem x2JR_2_76_6 : x2JKeyRangeOK 2 76 6 = true := by
  decide +kernel

end ThreeCopyQutritWerner.X2
