module

public import ThreeCopyQutritWerner.CertificateX2InputJSym

@[expose] public section


/-! Kernel checks of the images' sign laws, part 2. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThreeCopyQutritWerner.X2

theorem x2JC_1_143_36_36 : x2JColRangeOK 1 ⟨143, by decide⟩ 36 36 = true := by
  decide +kernel

theorem x2JC_1_154_41_41 : x2JColRangeOK 1 ⟨154, by decide⟩ 41 41 = true := by
  decide +kernel

theorem x2JC_1_155_72_36 : x2JColRangeOK 1 ⟨155, by decide⟩ 72 36 = true := by
  decide +kernel

theorem x2JC_1_160_42_7 : x2JColRangeOK 1 ⟨160, by decide⟩ 42 7 = true := by
  decide +kernel

theorem x2JC_1_160_98_7 : x2JColRangeOK 1 ⟨160, by decide⟩ 98 7 = true := by
  decide +kernel

theorem x2JC_1_162_0_69 : x2JColRangeOK 1 ⟨162, by decide⟩ 0 69 = true := by
  decide +kernel

theorem x2JC_1_162_138_15 : x2JColRangeOK 1 ⟨162, by decide⟩ 138 15 = true := by
  decide +kernel

theorem x2JC_2_101_19_19 : x2JColRangeOK 2 ⟨101, by decide⟩ 19 19 = true := by
  decide +kernel

theorem x2JC_2_107_87_11 : x2JColRangeOK 2 ⟨107, by decide⟩ 87 11 = true := by
  decide +kernel

theorem x2JR_1_126_9 : x2JKeyRangeOK 1 126 9 = true := by
  decide +kernel

theorem x2JR_2_119_1 : x2JKeyRangeOK 2 119 1 = true := by
  decide +kernel

end ThreeCopyQutritWerner.X2
