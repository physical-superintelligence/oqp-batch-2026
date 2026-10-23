module

public import ThreeCopyQutritWerner.CertificateX2InputJSym

@[expose] public section


/-! Kernel checks of the images' sign laws, part 4. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThreeCopyQutritWerner.X2

theorem x2JC_1_125_56_28 : x2JColRangeOK 1 ⟨125, by decide⟩ 56 28 = true := by
  decide +kernel

theorem x2JC_1_154_0_41 : x2JColRangeOK 1 ⟨154, by decide⟩ 0 41 = true := by
  decide +kernel

theorem x2JC_1_159_130_13 : x2JColRangeOK 1 ⟨159, by decide⟩ 130 13 = true := by
  decide +kernel

theorem x2JC_1_159_26_13 : x2JColRangeOK 1 ⟨159, by decide⟩ 26 13 = true := by
  decide +kernel

theorem x2JC_2_102_10_10 : x2JColRangeOK 2 ⟨102, by decide⟩ 10 10 = true := by
  decide +kernel

theorem x2JC_2_107_58_29 : x2JColRangeOK 2 ⟨107, by decide⟩ 58 29 = true := by
  decide +kernel

theorem x2JC_2_108_56_11 : x2JColRangeOK 2 ⟨108, by decide⟩ 56 11 = true := by
  decide +kernel

theorem x2JR_1_105_4 : x2JKeyRangeOK 1 105 4 = true := by
  decide +kernel

theorem x2JR_2_0_52 : x2JKeyRangeOK 2 0 52 = true := by
  decide +kernel

theorem x2JR_2_52_15 : x2JKeyRangeOK 2 52 15 = true := by
  decide +kernel

theorem x2JR_2_99_2 : x2JKeyRangeOK 2 99 2 = true := by
  decide +kernel

end ThreeCopyQutritWerner.X2
