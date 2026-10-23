module

public import ThreeCopyQutritWerner.CertificateX2InputJSym

@[expose] public section


/-! Kernel checks of the images' sign laws, part 0. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThreeCopyQutritWerner.X2

theorem x2JC_1_112_0_51 : x2JColRangeOK 1 ⟨112, by decide⟩ 0 51 = true := by
  decide +kernel

theorem x2JC_1_125_28_28 : x2JColRangeOK 1 ⟨125, by decide⟩ 28 28 = true := by
  decide +kernel

theorem x2JC_1_143_108_36 : x2JColRangeOK 1 ⟨143, by decide⟩ 108 36 = true := by
  decide +kernel

theorem x2JC_1_154_123_41 : x2JColRangeOK 1 ⟨154, by decide⟩ 123 41 = true := by
  decide +kernel

theorem x2JC_1_155_144_19 : x2JColRangeOK 1 ⟨155, by decide⟩ 144 19 = true := by
  decide +kernel

theorem x2JC_1_159_117_13 : x2JColRangeOK 1 ⟨159, by decide⟩ 117 13 = true := by
  decide +kernel

theorem x2JC_1_159_13_13 : x2JColRangeOK 1 ⟨159, by decide⟩ 13 13 = true := by
  decide +kernel

theorem x2JC_2_102_0_10 : x2JColRangeOK 2 ⟨102, by decide⟩ 0 10 = true := by
  decide +kernel

theorem x2JR_1_113_7 : x2JKeyRangeOK 1 113 7 = true := by
  decide +kernel

theorem x2JR_2_82_10 : x2JKeyRangeOK 2 82 10 = true := by
  decide +kernel

end ThreeCopyQutritWerner.X2
