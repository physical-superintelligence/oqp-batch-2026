module

public import ThreeCopyQutritWerner.CertificateX2InputJSym

@[expose] public section


/-! Kernel checks of the images' sign laws, part 11. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThreeCopyQutritWerner.X2

theorem x2JC_1_124_160_32 : x2JColRangeOK 1 ⟨124, by decide⟩ 160 32 = true := by
  decide +kernel

theorem x2JC_1_125_112_28 : x2JColRangeOK 1 ⟨125, by decide⟩ 112 28 = true := by
  decide +kernel

theorem x2JC_1_142_82_41 : x2JColRangeOK 1 ⟨142, by decide⟩ 82 41 = true := by
  decide +kernel

theorem x2JC_1_159_52_13 : x2JColRangeOK 1 ⟨159, by decide⟩ 52 13 = true := by
  decide +kernel

theorem x2JC_1_160_70_7 : x2JColRangeOK 1 ⟨160, by decide⟩ 70 7 = true := by
  decide +kernel

theorem x2JC_2_109_0_46 : x2JColRangeOK 2 ⟨109, by decide⟩ 0 46 = true := by
  decide +kernel

theorem x2JR_1_109_2 : x2JKeyRangeOK 1 109 2 = true := by
  decide +kernel

theorem x2JR_1_111_1 : x2JKeyRangeOK 1 111 1 = true := by
  decide +kernel

theorem x2JR_1_151_3 : x2JKeyRangeOK 1 151 3 = true := by
  decide +kernel

theorem x2JR_1_161_1 : x2JKeyRangeOK 1 161 1 = true := by
  decide +kernel

theorem x2JR_2_110_1 : x2JKeyRangeOK 2 110 1 = true := by
  decide +kernel

theorem x2JR_2_93_6 : x2JKeyRangeOK 2 93 6 = true := by
  decide +kernel

end ThreeCopyQutritWerner.X2
