module

public import ThreeCopyQutritWerner.CertificateX2InputJSym

@[expose] public section


/-! Kernel checks of the images' sign laws, part 7. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThreeCopyQutritWerner.X2

theorem x2JC_1_124_32_32 : x2JColRangeOK 1 ⟨124, by decide⟩ 32 32 = true := by
  decide +kernel

theorem x2JC_1_154_164_10 : x2JColRangeOK 1 ⟨154, by decide⟩ 164 10 = true := by
  decide +kernel

theorem x2JC_1_159_91_13 : x2JColRangeOK 1 ⟨159, by decide⟩ 91 13 = true := by
  decide +kernel

theorem x2JC_1_160_112_2 : x2JColRangeOK 1 ⟨160, by decide⟩ 112 2 = true := by
  decide +kernel

theorem x2JC_1_160_14_7 : x2JColRangeOK 1 ⟨160, by decide⟩ 14 7 = true := by
  decide +kernel

theorem x2JC_1_160_63_7 : x2JColRangeOK 1 ⟨160, by decide⟩ 63 7 = true := by
  decide +kernel

theorem x2JC_1_163_0_41 : x2JColRangeOK 1 ⟨163, by decide⟩ 0 41 = true := by
  decide +kernel

theorem x2JC_2_104_0_88 : x2JColRangeOK 2 ⟨104, by decide⟩ 0 88 = true := by
  decide +kernel

theorem x2JC_2_111_0_46 : x2JColRangeOK 2 ⟨111, by decide⟩ 0 46 = true := by
  decide +kernel

theorem x2JR_1_100_5 : x2JKeyRangeOK 1 100 5 = true := by
  decide +kernel

theorem x2JR_1_135_3 : x2JKeyRangeOK 1 135 3 = true := by
  decide +kernel

end ThreeCopyQutritWerner.X2
