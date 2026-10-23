module

public import ThreeCopyQutritWerner.CertificateX2InputJSym

@[expose] public section


/-! Kernel checks of the images' sign laws, part 3. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThreeCopyQutritWerner.X2

theorem x2JC_1_143_72_36 : x2JColRangeOK 1 ⟨143, by decide⟩ 72 36 = true := by
  decide +kernel

theorem x2JC_1_154_82_41 : x2JColRangeOK 1 ⟨154, by decide⟩ 82 41 = true := by
  decide +kernel

theorem x2JC_1_155_108_36 : x2JColRangeOK 1 ⟨155, by decide⟩ 108 36 = true := by
  decide +kernel

theorem x2JC_1_159_0_13 : x2JColRangeOK 1 ⟨159, by decide⟩ 0 13 = true := by
  decide +kernel

theorem x2JC_1_159_104_13 : x2JColRangeOK 1 ⟨159, by decide⟩ 104 13 = true := by
  decide +kernel

theorem x2JC_1_160_105_7 : x2JColRangeOK 1 ⟨160, by decide⟩ 105 7 = true := by
  decide +kernel

theorem x2JC_1_162_69_69 : x2JColRangeOK 1 ⟨162, by decide⟩ 69 69 = true := by
  decide +kernel

theorem x2JC_2_101_38_15 : x2JColRangeOK 2 ⟨101, by decide⟩ 38 15 = true := by
  decide +kernel

theorem x2JC_2_109_46_11 : x2JColRangeOK 2 ⟨109, by decide⟩ 46 11 = true := by
  decide +kernel

theorem x2JC_2_112_39_31 : x2JColRangeOK 2 ⟨112, by decide⟩ 39 31 = true := by
  decide +kernel

theorem x2JR_1_138_4 : x2JKeyRangeOK 1 138 4 = true := by
  decide +kernel

end ThreeCopyQutritWerner.X2
