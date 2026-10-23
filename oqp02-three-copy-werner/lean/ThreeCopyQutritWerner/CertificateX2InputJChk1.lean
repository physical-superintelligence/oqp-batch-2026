module

public import ThreeCopyQutritWerner.CertificateX2InputJSym

@[expose] public section


/-! Kernel checks of the images' sign laws, part 1. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThreeCopyQutritWerner.X2

theorem x2JC_1_112_51_51 : x2JColRangeOK 1 ⟨112, by decide⟩ 51 51 = true := by
  decide +kernel

theorem x2JC_1_125_0_28 : x2JColRangeOK 1 ⟨125, by decide⟩ 0 28 = true := by
  decide +kernel

theorem x2JC_1_160_35_7 : x2JColRangeOK 1 ⟨160, by decide⟩ 35 7 = true := by
  decide +kernel

theorem x2JC_1_160_91_7 : x2JColRangeOK 1 ⟨160, by decide⟩ 91 7 = true := by
  decide +kernel

theorem x2JC_1_163_123_13 : x2JColRangeOK 1 ⟨163, by decide⟩ 123 13 = true := by
  decide +kernel

theorem x2JC_2_101_0_19 : x2JColRangeOK 2 ⟨101, by decide⟩ 0 19 = true := by
  decide +kernel

theorem x2JC_2_106_88_20 : x2JColRangeOK 2 ⟨106, by decide⟩ 88 20 = true := by
  decide +kernel

theorem x2JC_2_107_29_29 : x2JColRangeOK 2 ⟨107, by decide⟩ 29 29 = true := by
  decide +kernel

theorem x2JC_2_108_0_56 : x2JColRangeOK 2 ⟨108, by decide⟩ 0 56 = true := by
  decide +kernel

theorem x2JC_2_111_46_35 : x2JColRangeOK 2 ⟨111, by decide⟩ 46 35 = true := by
  decide +kernel

theorem x2JR_2_113_4 : x2JKeyRangeOK 2 113 4 = true := by
  decide +kernel

end ThreeCopyQutritWerner.X2
