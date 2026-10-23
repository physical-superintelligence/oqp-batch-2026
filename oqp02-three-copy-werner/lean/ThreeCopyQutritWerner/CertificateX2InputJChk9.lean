module

public import ThreeCopyQutritWerner.CertificateX2InputJSym

@[expose] public section


/-! Kernel checks of the images' sign laws, part 9. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThreeCopyQutritWerner.X2

theorem x2JC_1_124_96_32 : x2JColRangeOK 1 ⟨124, by decide⟩ 96 32 = true := by
  decide +kernel

theorem x2JC_1_125_140_28 : x2JColRangeOK 1 ⟨125, by decide⟩ 140 28 = true := by
  decide +kernel

theorem x2JC_1_142_0_41 : x2JColRangeOK 1 ⟨142, by decide⟩ 0 41 = true := by
  decide +kernel

theorem x2JC_1_159_65_13 : x2JColRangeOK 1 ⟨159, by decide⟩ 65 13 = true := by
  decide +kernel

theorem x2JC_1_160_0_7 : x2JColRangeOK 1 ⟨160, by decide⟩ 0 7 = true := by
  decide +kernel

theorem x2JC_1_160_49_7 : x2JColRangeOK 1 ⟨160, by decide⟩ 49 7 = true := by
  decide +kernel

theorem x2JC_2_105_0_32 : x2JColRangeOK 2 ⟨105, by decide⟩ 0 32 = true := by
  decide +kernel

theorem x2JC_2_105_64_20 : x2JColRangeOK 2 ⟨105, by decide⟩ 64 20 = true := by
  decide +kernel

theorem x2JR_1_144_7 : x2JKeyRangeOK 1 144 7 = true := by
  decide +kernel

theorem x2JR_1_164_5 : x2JKeyRangeOK 1 164 5 = true := by
  decide +kernel

end ThreeCopyQutritWerner.X2
