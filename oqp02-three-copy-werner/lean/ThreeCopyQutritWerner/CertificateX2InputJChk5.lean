module

public import ThreeCopyQutritWerner.CertificateX2InputJSym

@[expose] public section


/-! Kernel checks of the images' sign laws, part 5. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThreeCopyQutritWerner.X2

theorem x2JC_1_142_123_41 : x2JColRangeOK 1 ⟨142, by decide⟩ 123 41 = true := by
  decide +kernel

theorem x2JC_1_155_0_36 : x2JColRangeOK 1 ⟨155, by decide⟩ 0 36 = true := by
  decide +kernel

theorem x2JC_1_160_21_7 : x2JColRangeOK 1 ⟨160, by decide⟩ 21 7 = true := by
  decide +kernel

theorem x2JC_1_160_77_7 : x2JColRangeOK 1 ⟨160, by decide⟩ 77 7 = true := by
  decide +kernel

theorem x2JC_1_163_41_41 : x2JColRangeOK 1 ⟨163, by decide⟩ 41 41 = true := by
  decide +kernel

theorem x2JC_2_107_0_29 : x2JColRangeOK 2 ⟨107, by decide⟩ 0 29 = true := by
  decide +kernel

theorem x2JC_2_112_0_39 : x2JColRangeOK 2 ⟨112, by decide⟩ 0 39 = true := by
  decide +kernel

theorem x2JR_1_120_4 : x2JKeyRangeOK 1 120 4 = true := by
  decide +kernel

theorem x2JR_1_156_3 : x2JKeyRangeOK 1 156 3 = true := by
  decide +kernel

theorem x2JR_1_70_30 : x2JKeyRangeOK 1 70 30 = true := by
  decide +kernel

theorem x2JR_2_92_1 : x2JKeyRangeOK 2 92 1 = true := by
  decide +kernel

end ThreeCopyQutritWerner.X2
