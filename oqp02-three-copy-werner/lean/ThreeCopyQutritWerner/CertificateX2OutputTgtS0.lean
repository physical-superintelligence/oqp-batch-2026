module

public import ThreeCopyQutritWerner.CertificateX2OutputConcrete
public import ThreeCopyQutritWerner.CertificateX2OutputSplit

@[expose] public section


/-! Output stage: targets `x2Target x2DataConcrete b = T8 / 8` of h blocks
003-0, 012-0, 016-0, 025-0, 035-0, 045-0, 056-0, 111-2, 113-1, 115-1, 122-1, 126-0, 135-0, 145-0, 156-0, 222-2, 224-1, 226-1, 235-0, 255-0, 266-1, 334-1, 336-1, 355-1. The kernel computes `Jᵀ (M ⊗ M ⊗ M) J` from the images of CertificateX2Images and the local tables
of CertificateX2Reduced (W = 72). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThreeCopyQutritWerner.X2.Tgt

/-- h block `003-0`. -/
def blk_003k0 : x2Key 0 := ⟨0, by decide⟩

/-- `T8 = Jᵀ (M ⊗ M ⊗ M) J` of block `003-0`. -/
def t8_003k0 : List (List ℤ) := [
  [32]]

theorem amb_003k0 : x2KeyMult 0 blk_003k0 0 * x2KeyMult 0 blk_003k0 1 * x2KeyMult 0 blk_003k0 2 = 5 := by
  decide +kernel

theorem chk_003k0 : ∀ c < x2KeySize 0 blk_003k0, ∀ c' < x2KeySize 0 blk_003k0,
    x2TgtNum 72 1 blk_003k0 (x2JAll.getD (x2KeyGlobal 0 blk_003k0) []) c c' = (t8_003k0.getD c []).getD c' 0 := by
  decide +kernel

theorem tgt_003k0 : x2Target x2DataConcrete blk_003k0 =
    Matrix.of fun (c c' : x2Col 0 blk_003k0) => (((t8_003k0.getD c []).getD c' 0 : ℤ) : ℚ) / 8 :=
  x2Target_eq_lit x2DataConcrete blk_003k0 72 1 _ (fun c c' => (t8_003k0.getD c []).getD c' 0)
    (x2Target_eq_of_check x2DataConcrete blk_003k0 72 1 _ (by norm_num) (x2JAll_length_h blk_003k0)
      (x2ImageCols_concrete blk_003k0) (by rw [amb_003k0]; norm_num) (by rw [amb_003k0]; norm_num)) chk_003k0

/-- h block `012-0`. -/
def blk_012k0 : x2Key 0 := ⟨4, by decide⟩

/-- `T8 = Jᵀ (M ⊗ M ⊗ M) J` of block `012-0`. -/
def t8_012k0 : List (List ℤ) := [
  [128]]

theorem amb_012k0 : x2KeyMult 0 blk_012k0 0 * x2KeyMult 0 blk_012k0 1 * x2KeyMult 0 blk_012k0 2 = 20 := by
  decide +kernel

theorem chk_012k0 : ∀ c < x2KeySize 0 blk_012k0, ∀ c' < x2KeySize 0 blk_012k0,
    x2TgtNum 72 2 blk_012k0 (x2JAll.getD (x2KeyGlobal 0 blk_012k0) []) c c' = (t8_012k0.getD c []).getD c' 0 := by
  decide +kernel

theorem tgt_012k0 : x2Target x2DataConcrete blk_012k0 =
    Matrix.of fun (c c' : x2Col 0 blk_012k0) => (((t8_012k0.getD c []).getD c' 0 : ℤ) : ℚ) / 8 :=
  x2Target_eq_lit x2DataConcrete blk_012k0 72 2 _ (fun c c' => (t8_012k0.getD c []).getD c' 0)
    (x2Target_eq_of_check x2DataConcrete blk_012k0 72 2 _ (by norm_num) (x2JAll_length_h blk_012k0)
      (x2ImageCols_concrete blk_012k0) (by rw [amb_012k0]; norm_num) (by rw [amb_012k0]; norm_num)) chk_012k0

/-- h block `016-0`. -/
def blk_016k0 : x2Key 0 := ⟨8, by decide⟩

/-- `T8 = Jᵀ (M ⊗ M ⊗ M) J` of block `016-0`. -/
def t8_016k0 : List (List ℤ) := [
  [3328, -3584],
  [-3584, 3072]]

theorem amb_016k0 : x2KeyMult 0 blk_016k0 0 * x2KeyMult 0 blk_016k0 1 * x2KeyMult 0 blk_016k0 2 = 44 := by
  decide +kernel

theorem chk_016k0 : ∀ c < x2KeySize 0 blk_016k0, ∀ c' < x2KeySize 0 blk_016k0,
    x2TgtNum 72 2 blk_016k0 (x2JAll.getD (x2KeyGlobal 0 blk_016k0) []) c c' = (t8_016k0.getD c []).getD c' 0 := by
  decide +kernel

theorem tgt_016k0 : x2Target x2DataConcrete blk_016k0 =
    Matrix.of fun (c c' : x2Col 0 blk_016k0) => (((t8_016k0.getD c []).getD c' 0 : ℤ) : ℚ) / 8 :=
  x2Target_eq_lit x2DataConcrete blk_016k0 72 2 _ (fun c c' => (t8_016k0.getD c []).getD c' 0)
    (x2Target_eq_of_check x2DataConcrete blk_016k0 72 2 _ (by norm_num) (x2JAll_length_h blk_016k0)
      (x2ImageCols_concrete blk_016k0) (by rw [amb_016k0]; norm_num) (by rw [amb_016k0]; norm_num)) chk_016k0

/-- h block `025-0`. -/
def blk_025k0 : x2Key 0 := ⟨12, by decide⟩

/-- `T8 = Jᵀ (M ⊗ M ⊗ M) J` of block `025-0`. -/
def t8_025k0 : List (List ℤ) := [
  [1920, 5120, -3840],
  [5120, 3840, -8960],
  [-3840, -8960, 19200]]

theorem amb_025k0 : x2KeyMult 0 blk_025k0 0 * x2KeyMult 0 blk_025k0 1 * x2KeyMult 0 blk_025k0 2 = 50 := by
  decide +kernel

theorem chk_025k0 : ∀ c < x2KeySize 0 blk_025k0, ∀ c' < x2KeySize 0 blk_025k0,
    x2TgtNum 72 3 blk_025k0 (x2JAll.getD (x2KeyGlobal 0 blk_025k0) []) c c' = (t8_025k0.getD c []).getD c' 0 := by
  decide +kernel

theorem tgt_025k0 : x2Target x2DataConcrete blk_025k0 =
    Matrix.of fun (c c' : x2Col 0 blk_025k0) => (((t8_025k0.getD c []).getD c' 0 : ℤ) : ℚ) / 8 :=
  x2Target_eq_lit x2DataConcrete blk_025k0 72 3 _ (fun c c' => (t8_025k0.getD c []).getD c' 0)
    (x2Target_eq_of_check x2DataConcrete blk_025k0 72 3 _ (by norm_num) (x2JAll_length_h blk_025k0)
      (x2ImageCols_concrete blk_025k0) (by rw [amb_025k0]; norm_num) (by rw [amb_025k0]; norm_num)) chk_025k0

/-- h block `035-0`. -/
def blk_035k0 : x2Key 0 := ⟨16, by decide⟩

/-- `T8 = Jᵀ (M ⊗ M ⊗ M) J` of block `035-0`. -/
def t8_035k0 : List (List ℤ) := [
  [23040, 11520],
  [11520, 5760]]

theorem amb_035k0 : x2KeyMult 0 blk_035k0 0 * x2KeyMult 0 blk_035k0 1 * x2KeyMult 0 blk_035k0 2 = 50 := by
  decide +kernel

theorem chk_035k0 : ∀ c < x2KeySize 0 blk_035k0, ∀ c' < x2KeySize 0 blk_035k0,
    x2TgtNum 72 3 blk_035k0 (x2JAll.getD (x2KeyGlobal 0 blk_035k0) []) c c' = (t8_035k0.getD c []).getD c' 0 := by
  decide +kernel

theorem tgt_035k0 : x2Target x2DataConcrete blk_035k0 =
    Matrix.of fun (c c' : x2Col 0 blk_035k0) => (((t8_035k0.getD c []).getD c' 0 : ℤ) : ℚ) / 8 :=
  x2Target_eq_lit x2DataConcrete blk_035k0 72 3 _ (fun c c' => (t8_035k0.getD c []).getD c' 0)
    (x2Target_eq_of_check x2DataConcrete blk_035k0 72 3 _ (by norm_num) (x2JAll_length_h blk_035k0)
      (x2ImageCols_concrete blk_035k0) (by rw [amb_035k0]; norm_num) (by rw [amb_035k0]; norm_num)) chk_035k0

/-- h block `045-0`. -/
def blk_045k0 : x2Key 0 := ⟨20, by decide⟩

/-- `T8 = Jᵀ (M ⊗ M ⊗ M) J` of block `045-0`. -/
def t8_045k0 : List (List ℤ) := [
  [22464, 76032, 3456, 3456, -34560, -41472],
  [76032, 303552, -1536, 40896, -109632, -161856],
  [3456, -1536, 18944, -13056, 2560, 56832],
  [3456, 40896, -13056, 33984, -22080, -134208],
  [-34560, -109632, 2560, -22080, 44480, 85440],
  [-41472, -161856, 56832, -134208, 85440, 455616]]

theorem amb_045k0 : x2KeyMult 0 blk_045k0 0 * x2KeyMult 0 blk_045k0 1 * x2KeyMult 0 blk_045k0 2 = 150 := by
  decide +kernel

theorem chk_045k0 : ∀ c < x2KeySize 0 blk_045k0, ∀ c' < x2KeySize 0 blk_045k0,
    x2TgtNum 72 4 blk_045k0 (x2JAll.getD (x2KeyGlobal 0 blk_045k0) []) c c' = (t8_045k0.getD c []).getD c' 0 := by
  decide +kernel

theorem tgt_045k0 : x2Target x2DataConcrete blk_045k0 =
    Matrix.of fun (c c' : x2Col 0 blk_045k0) => (((t8_045k0.getD c []).getD c' 0 : ℤ) : ℚ) / 8 :=
  x2Target_eq_lit x2DataConcrete blk_045k0 72 4 _ (fun c c' => (t8_045k0.getD c []).getD c' 0)
    (x2Target_eq_of_check x2DataConcrete blk_045k0 72 4 _ (by norm_num) (x2JAll_length_h blk_045k0)
      (x2ImageCols_concrete blk_045k0) (by rw [amb_045k0]; norm_num) (by rw [amb_045k0]; norm_num)) chk_045k0

/-- h block `056-0`. -/
def blk_056k0 : x2Key 0 := ⟨24, by decide⟩

/-- `T8 = Jᵀ (M ⊗ M ⊗ M) J` of block `056-0`. -/
def t8_056k0 : List (List ℤ) := [
  [5632, 17408, -10752, 2560],
  [17408, 125952, -37888, 48640],
  [-10752, -37888, 31232, -10240],
  [2560, 48640, -10240, 23040]]

theorem amb_056k0 : x2KeyMult 0 blk_056k0 0 * x2KeyMult 0 blk_056k0 1 * x2KeyMult 0 blk_056k0 2 = 110 := by
  decide +kernel

theorem chk_056k0 : ∀ c < x2KeySize 0 blk_056k0, ∀ c' < x2KeySize 0 blk_056k0,
    x2TgtNum 72 4 blk_056k0 (x2JAll.getD (x2KeyGlobal 0 blk_056k0) []) c c' = (t8_056k0.getD c []).getD c' 0 := by
  decide +kernel

theorem tgt_056k0 : x2Target x2DataConcrete blk_056k0 =
    Matrix.of fun (c c' : x2Col 0 blk_056k0) => (((t8_056k0.getD c []).getD c' 0 : ℤ) : ℚ) / 8 :=
  x2Target_eq_lit x2DataConcrete blk_056k0 72 4 _ (fun c c' => (t8_056k0.getD c []).getD c' 0)
    (x2Target_eq_of_check x2DataConcrete blk_056k0 72 4 _ (by norm_num) (x2JAll_length_h blk_056k0)
      (x2ImageCols_concrete blk_056k0) (by rw [amb_056k0]; norm_num) (by rw [amb_056k0]; norm_num)) chk_056k0

/-- h block `111-2`. -/
def blk_111k2 : x2Key 0 := ⟨28, by decide⟩

/-- `T8 = Jᵀ (M ⊗ M ⊗ M) J` of block `111-2`. -/
def t8_111k2 : List (List ℤ) := [
  [7680]]

theorem amb_111k2 : x2KeyMult 0 blk_111k2 0 * x2KeyMult 0 blk_111k2 1 * x2KeyMult 0 blk_111k2 2 = 64 := by
  decide +kernel

theorem chk_111k2 : ∀ c < x2KeySize 0 blk_111k2, ∀ c' < x2KeySize 0 blk_111k2,
    x2TgtNum 72 4 blk_111k2 (x2JAll.getD (x2KeyGlobal 0 blk_111k2) []) c c' = (t8_111k2.getD c []).getD c' 0 := by
  decide +kernel

theorem tgt_111k2 : x2Target x2DataConcrete blk_111k2 =
    Matrix.of fun (c c' : x2Col 0 blk_111k2) => (((t8_111k2.getD c []).getD c' 0 : ℤ) : ℚ) / 8 :=
  x2Target_eq_lit x2DataConcrete blk_111k2 72 4 _ (fun c c' => (t8_111k2.getD c []).getD c' 0)
    (x2Target_eq_of_check x2DataConcrete blk_111k2 72 4 _ (by norm_num) (x2JAll_length_h blk_111k2)
      (x2ImageCols_concrete blk_111k2) (by rw [amb_111k2]; norm_num) (by rw [amb_111k2]; norm_num)) chk_111k2

/-- h block `113-1`. -/
def blk_113k1 : x2Key 0 := ⟨32, by decide⟩

/-- `T8 = Jᵀ (M ⊗ M ⊗ M) J` of block `113-1`. -/
def t8_113k1 : List (List ℤ) := [
  [1536]]

theorem amb_113k1 : x2KeyMult 0 blk_113k1 0 * x2KeyMult 0 blk_113k1 1 * x2KeyMult 0 blk_113k1 2 = 80 := by
  decide +kernel

theorem chk_113k1 : ∀ c < x2KeySize 0 blk_113k1, ∀ c' < x2KeySize 0 blk_113k1,
    x2TgtNum 72 4 blk_113k1 (x2JAll.getD (x2KeyGlobal 0 blk_113k1) []) c c' = (t8_113k1.getD c []).getD c' 0 := by
  decide +kernel

theorem tgt_113k1 : x2Target x2DataConcrete blk_113k1 =
    Matrix.of fun (c c' : x2Col 0 blk_113k1) => (((t8_113k1.getD c []).getD c' 0 : ℤ) : ℚ) / 8 :=
  x2Target_eq_lit x2DataConcrete blk_113k1 72 4 _ (fun c c' => (t8_113k1.getD c []).getD c' 0)
    (x2Target_eq_of_check x2DataConcrete blk_113k1 72 4 _ (by norm_num) (x2JAll_length_h blk_113k1)
      (x2ImageCols_concrete blk_113k1) (by rw [amb_113k1]; norm_num) (by rw [amb_113k1]; norm_num)) chk_113k1

/-- h block `115-1`. -/
def blk_115k1 : x2Key 0 := ⟨36, by decide⟩

/-- `T8 = Jᵀ (M ⊗ M ⊗ M) J` of block `115-1`. -/
def t8_115k1 : List (List ℤ) := [
  [20480, -5120],
  [-5120, 35840]]

theorem amb_115k1 : x2KeyMult 0 blk_115k1 0 * x2KeyMult 0 blk_115k1 1 * x2KeyMult 0 blk_115k1 2 = 160 := by
  decide +kernel

theorem chk_115k1 : ∀ c < x2KeySize 0 blk_115k1, ∀ c' < x2KeySize 0 blk_115k1,
    x2TgtNum 72 4 blk_115k1 (x2JAll.getD (x2KeyGlobal 0 blk_115k1) []) c c' = (t8_115k1.getD c []).getD c' 0 := by
  decide +kernel

theorem tgt_115k1 : x2Target x2DataConcrete blk_115k1 =
    Matrix.of fun (c c' : x2Col 0 blk_115k1) => (((t8_115k1.getD c []).getD c' 0 : ℤ) : ℚ) / 8 :=
  x2Target_eq_lit x2DataConcrete blk_115k1 72 4 _ (fun c c' => (t8_115k1.getD c []).getD c' 0)
    (x2Target_eq_of_check x2DataConcrete blk_115k1 72 4 _ (by norm_num) (x2JAll_length_h blk_115k1)
      (x2ImageCols_concrete blk_115k1) (by rw [amb_115k1]; norm_num) (by rw [amb_115k1]; norm_num)) chk_115k1

/-- h block `122-1`. -/
def blk_122k1 : x2Key 0 := ⟨40, by decide⟩

/-- `T8 = Jᵀ (M ⊗ M ⊗ M) J` of block `122-1`. -/
def t8_122k1 : List (List ℤ) := [
  [9728, -512],
  [-512, 1536]]

theorem amb_122k1 : x2KeyMult 0 blk_122k1 0 * x2KeyMult 0 blk_122k1 1 * x2KeyMult 0 blk_122k1 2 = 100 := by
  decide +kernel

theorem chk_122k1 : ∀ c < x2KeySize 0 blk_122k1, ∀ c' < x2KeySize 0 blk_122k1,
    x2TgtNum 72 5 blk_122k1 (x2JAll.getD (x2KeyGlobal 0 blk_122k1) []) c c' = (t8_122k1.getD c []).getD c' 0 := by
  decide +kernel

theorem tgt_122k1 : x2Target x2DataConcrete blk_122k1 =
    Matrix.of fun (c c' : x2Col 0 blk_122k1) => (((t8_122k1.getD c []).getD c' 0 : ℤ) : ℚ) / 8 :=
  x2Target_eq_lit x2DataConcrete blk_122k1 72 5 _ (fun c c' => (t8_122k1.getD c []).getD c' 0)
    (x2Target_eq_of_check x2DataConcrete blk_122k1 72 5 _ (by norm_num) (x2JAll_length_h blk_122k1)
      (x2ImageCols_concrete blk_122k1) (by rw [amb_122k1]; norm_num) (by rw [amb_122k1]; norm_num)) chk_122k1

/-- h block `126-0`. -/
def blk_126k0 : x2Key 0 := ⟨44, by decide⟩

/-- `T8 = Jᵀ (M ⊗ M ⊗ M) J` of block `126-0`. -/
def t8_126k0 : List (List ℤ) := [
  [118272, 73728, 64512, 61440, 27648, 138240, 11520, 73728, -175104],
  [73728, 875520, 368640, -193536, -96768, 0, 59904, -285696, -18432],
  [64512, 368640, 345600, 147456, 225792, 138240, 274176, -23040, -207360],
  [61440, -193536, 147456, 410112, 78336, 69120, -73728, 410112, -101376],
  [27648, -96768, 225792, 78336, 156672, 64512, 110592, -27648, -64512],
  [138240, 0, 138240, 69120, 64512, 161280, 23040, 133632, -331776],
  [11520, 59904, 274176, -73728, 110592, 23040, -44928, -6912, -71424],
  [73728, -285696, -23040, 410112, -27648, 133632, -6912, 414720, -78336],
  [-175104, -18432, -207360, -101376, -64512, -331776, -71424, -78336, 400896]]

theorem amb_126k0 : x2KeyMult 0 blk_126k0 0 * x2KeyMult 0 blk_126k0 1 * x2KeyMult 0 blk_126k0 2 = 220 := by
  decide +kernel

theorem chk_126k0 : ∀ c < x2KeySize 0 blk_126k0, ∀ c' < x2KeySize 0 blk_126k0,
    x2TgtNum 72 5 blk_126k0 (x2JAll.getD (x2KeyGlobal 0 blk_126k0) []) c c' = (t8_126k0.getD c []).getD c' 0 := by
  decide +kernel

theorem tgt_126k0 : x2Target x2DataConcrete blk_126k0 =
    Matrix.of fun (c c' : x2Col 0 blk_126k0) => (((t8_126k0.getD c []).getD c' 0 : ℤ) : ℚ) / 8 :=
  x2Target_eq_lit x2DataConcrete blk_126k0 72 5 _ (fun c c' => (t8_126k0.getD c []).getD c' 0)
    (x2Target_eq_of_check x2DataConcrete blk_126k0 72 5 _ (by norm_num) (x2JAll_length_h blk_126k0)
      (x2ImageCols_concrete blk_126k0) (by rw [amb_126k0]; norm_num) (by rw [amb_126k0]; norm_num)) chk_126k0

/-- h block `135-0`. -/
def blk_135k0 : x2Key 0 := ⟨48, by decide⟩

/-- `T8 = Jᵀ (M ⊗ M ⊗ M) J` of block `135-0`. -/
def t8_135k0 : List (List ℤ) := [
  [140160, -28032, 228672, -36672, -96768, 115200, -21120, 28608],
  [-28032, 84864, -126720, 11136, 69120, -29952, 24576, 2688],
  [228672, -126720, 607104, -56448, -202176, 212544, -66624, 51840],
  [-36672, 11136, -56448, 19200, 32832, -52416, 11712, -768],
  [-96768, 69120, -202176, 32832, 152064, -89856, 26496, -8640],
  [115200, -29952, 212544, -52416, -89856, 165888, -35712, 16704],
  [-21120, 24576, -66624, 11712, 26496, -35712, 18688, -3648],
  [28608, 2688, 51840, -768, -8640, 16704, -3648, 17664]]

theorem amb_135k0 : x2KeyMult 0 blk_135k0 0 * x2KeyMult 0 blk_135k0 1 * x2KeyMult 0 blk_135k0 2 = 200 := by
  decide +kernel

theorem chk_135k0 : ∀ c < x2KeySize 0 blk_135k0, ∀ c' < x2KeySize 0 blk_135k0,
    x2TgtNum 72 5 blk_135k0 (x2JAll.getD (x2KeyGlobal 0 blk_135k0) []) c c' = (t8_135k0.getD c []).getD c' 0 := by
  decide +kernel

theorem tgt_135k0 : x2Target x2DataConcrete blk_135k0 =
    Matrix.of fun (c c' : x2Col 0 blk_135k0) => (((t8_135k0.getD c []).getD c' 0 : ℤ) : ℚ) / 8 :=
  x2Target_eq_lit x2DataConcrete blk_135k0 72 5 _ (fun c c' => (t8_135k0.getD c []).getD c' 0)
    (x2Target_eq_of_check x2DataConcrete blk_135k0 72 5 _ (by norm_num) (x2JAll_length_h blk_135k0)
      (x2ImageCols_concrete blk_135k0) (by rw [amb_135k0]; norm_num) (by rw [amb_135k0]; norm_num)) chk_135k0

/-- h block `145-0`. -/
def blk_145k0 : x2Key 0 := ⟨52, by decide⟩

/-- `T8 = Jᵀ (M ⊗ M ⊗ M) J` of block `145-0`. -/
def t8_145k0 : List (List ℤ) := [
  [275712, 325056, -19200, 41856, -336768, -55104, -308928, -181824, 51456, 170112, -125760, 320256, 221760, 65472, -165120, -102528, 211584, -164160, 28416, 420672, 201600, 18624, 33408, -174336, -120192],
  [325056, 1310880, -79296, 381216, -351936, -37440, -129984, -317568, 5856, 273696, -126240, 926304, 725472, 669792, -161184, -496704, 269280, -147168, -118848, 623712, 355680, -255360, 218880, -40224, -464448],
  [-19200, -79296, 33024, -48000, 11136, -23232, -52032, 81984, 14592, -25728, -64704, -76032, -92736, -71616, -8448, 56448, 11136, -20160, 60672, -101184, -8064, 24384, -51840, -54528, 80256],
  [41856, 381216, -48000, 1482144, -10176, 9024, -45696, 116544, 12000, 784416, -49440, 335520, 462816, 821472, 438816, -234432, 242400, -37728, -68928, 434208, 43488, 95808, -118656, -113568, -352896],
  [-336768, -351936, 11136, -10176, 342336, 66624, 308928, 154752, -12288, -165504, 136128, -298752, -129600, -78720, 163392, 121728, -288960, 169344, -64128, -430848, -154944, -94080, -44928, 154176, 98880],
  [-55104, -37440, -23232, 9024, 66624, 125888, 94656, -28032, 6528, 1152, 83328, -11136, 17856, 18624, 108864, -78912, -51840, 35520, -182400, 13824, 11904, -31488, 73152, 25728, -23424],
  [-308928, -129984, -52032, -45696, 308928, 94656, 930624, -83904, 54336, -85632, 408192, -209088, 80064, -16320, -9024, -130176, -413376, 283968, -131712, -110400, -55296, -137472, 240192, 499584, -6144],
  [-181824, -317568, 81984, 116544, 154752, -28032, -83904, 794112, 960, 197952, 63552, -446400, -423936, -249216, 91968, 377280, -119424, -10944, 134592, -419520, -419328, -172992, -475200, -113088, 491136],
  [51456, 5856, 14592, 12000, -12288, 6528, 54336, 960, 51936, 41568, -23712, -3744, -23904, 3936, 66912, -25920, 1248, 12384, 8448, 19680, 46368, 34368, 22464, -65568, 28032],
  [170112, 273696, -25728, 784416, -165504, 1152, -85632, 197952, 41568, 1086432, 30432, -95328, 176544, 456672, 55392, -205632, 42720, -36576, -192, 523104, -262944, 109248, -229248, -120288, -38784],
  [-125760, -126240, -64704, -49440, 136128, 83328, 408192, 63552, -23712, 30432, 728160, -158112, 67104, -42528, -45600, -89856, -358368, 222624, -24000, 92064, -222624, 13440, 128448, 395040, 113664],
  [320256, 926304, -76032, 335520, -298752, -11136, -209088, -446400, -3744, -95328, -158112, 1038048, 634464, 363744, 59616, -359616, 286752, -152928, -137664, 597408, 559584, -235008, 358848, -136800, -456192],
  [221760, 725472, -92736, 462816, -129600, 17856, 80064, -423936, -23904, 176544, 67104, 634464, 667872, 659808, 48672, -358272, 197856, 23328, -93888, 474912, 280800, 118656, 262656, 95328, -484416],
  [65472, 669792, -71616, 821472, -78720, 18624, -16320, -249216, 3936, 456672, -42528, 363744, 659808, 816864, 143328, -456768, 90336, -65376, -49920, 272928, 271008, 116544, 123840, -44448, -494016],
  [-165120, -161184, -8448, 438816, 163392, 108864, -9024, 91968, 66912, 55392, -45600, 59616, 48672, 143328, 505248, 33984, -61536, 148896, -242112, -73632, 40032, -61824, 17856, -219936, -106752],
  [-102528, -496704, 56448, -234432, 121728, -78912, -130176, 377280, -25920, -205632, -89856, -359616, -358272, -456768, 33984, 508992, -40128, -21312, 102528, -417216, -184320, -97920, -263232, -17280, 330624],
  [211584, 269280, 11136, 242400, -288960, -51840, -413376, -119424, 1248, 42720, -358368, 286752, 197856, 90336, -61536, -40128, 446304, -269280, 4992, 174816, 324000, 93120, 25344, -202080, -178176],
  [-164160, -147168, -20160, -37728, 169344, 35520, 283968, -10944, 12384, -36576, 222624, -152928, 23328, -65376, 148896, -21312, -269280, 311904, -80064, -81504, -124704, -9216, 99648, 44064, -35136],
  [28416, -118848, 60672, -68928, -64128, -182400, -131712, 134592, 8448, -192, -24000, -137664, -93888, -49920, -242112, 102528, 4992, -80064, 447936, -159168, -77760, 214080, -154368, 34368, 214656],
  [420672, 623712, -101184, 434208, -430848, 13824, -110400, -419520, 19680, 523104, 92064, 597408, 474912, 272928, -73632, -417216, 174816, -81504, -159168, 1112736, 181728, -8832, 188928, -36192, -324480],
  [201600, 355680, -8064, 43488, -154944, 11904, -55296, -419328, 46368, -262944, -222624, 559584, 280800, 271008, 40032, -184320, 324000, -124704, -77760, 181728, 538848, 81216, 296640, -77472, -372096],
  [18624, -255360, 24384, 95808, -94080, -31488, -137472, -172992, 34368, 109248, 13440, -235008, 118656, 116544, -61824, -97920, 93120, -9216, 214080, -8832, 81216, 560256, 70272, -26112, -54912],
  [33408, 218880, -51840, -118656, -44928, 73152, 240192, -475200, 22464, -229248, 128448, 358848, 262656, 123840, 17856, -263232, 25344, 99648, -154368, 188928, 296640, 70272, 440640, 88704, -312768],
  [-174336, -40224, -54528, -113568, 154176, 25728, 499584, -113088, -65568, -120288, 395040, -136800, 95328, -44448, -219936, -17280, -202080, 44064, 34368, -36192, -77472, -26112, 88704, 637728, -3648],
  [-120192, -464448, 80256, -352896, 98880, -23424, -6144, 491136, 28032, -38784, 113664, -456192, -484416, -494016, -106752, 330624, -178176, -35136, 214656, -324480, -372096, -54912, -312768, -3648, 591936]]

theorem amb_145k0 : x2KeyMult 0 blk_145k0 0 * x2KeyMult 0 blk_145k0 1 * x2KeyMult 0 blk_145k0 2 = 600 := by
  decide +kernel

theorem chk_145k0 : ∀ c < x2KeySize 0 blk_145k0, ∀ c' < x2KeySize 0 blk_145k0,
    x2TgtNum 72 6 blk_145k0 (x2JAll.getD (x2KeyGlobal 0 blk_145k0) []) c c' = (t8_145k0.getD c []).getD c' 0 := by
  decide +kernel

theorem tgt_145k0 : x2Target x2DataConcrete blk_145k0 =
    Matrix.of fun (c c' : x2Col 0 blk_145k0) => (((t8_145k0.getD c []).getD c' 0 : ℤ) : ℚ) / 8 :=
  x2Target_eq_lit x2DataConcrete blk_145k0 72 6 _ (fun c c' => (t8_145k0.getD c []).getD c' 0)
    (x2Target_eq_of_check x2DataConcrete blk_145k0 72 6 _ (by norm_num) (x2JAll_length_h blk_145k0)
      (x2ImageCols_concrete blk_145k0) (by rw [amb_145k0]; norm_num) (by rw [amb_145k0]; norm_num)) chk_145k0

/-- h block `156-0`. -/
def blk_156k0 : x2Key 0 := ⟨56, by decide⟩

/-- `T8 = Jᵀ (M ⊗ M ⊗ M) J` of block `156-0`. -/
def t8_156k0 : List (List ℤ) := [
  [107520, 65280, 90624, -89600, -178176, 19200, 46080, -17920, 45312, -342144, -207744, -69120, -125952, 141696, -253440, 263040, 1152, 145920],
  [65280, 88320, -52992, -37888, -238080, 22016, 26112, -9472, 126720, -311040, -476160, -3840, -79872, 16896, -141312, 13056, -77568, 136704],
  [90624, -52992, 3777024, -138240, 353280, -129792, 382464, -368640, -635136, 786816, 938112, -778752, -314880, 302976, -746496, 794496, 11904, -371712],
  [-89600, -37888, -138240, 359936, 188928, 103424, -53760, -94208, 49152, 228096, 5376, 49152, 125952, -225024, 529920, -478464, -134400, 13824],
  [-178176, -238080, 353280, 188928, 1182720, 104448, -129024, -161280, -268800, 900864, 856320, 322560, 155136, -71424, 179712, 235776, -51456, -413184],
  [19200, 22016, -129792, 103424, 104448, 245504, 41472, -11008, 133632, -31872, -271488, 171264, 61440, 62592, 158208, -139392, -109440, 59904],
  [46080, 26112, 382464, -53760, -129024, 41472, 235008, 39936, 41472, 140544, -126720, -193536, -27648, 80640, 110592, -301824, 89856, 18432],
  [-17920, -9472, -368640, -94208, -161280, -11008, 39936, 219136, -135936, 110208, 78720, 49152, 3072, 5760, 205824, -164736, 306048, -58368],
  [45312, 126720, -635136, 49152, -268800, 133632, 41472, -135936, 1562880, -619776, -1081344, 108288, 454656, -419328, -27648, -142080, -585984, 536064],
  [-342144, -311040, 786816, 228096, 900864, -31872, 140544, 110208, -619776, 1805760, 1798848, 67968, 202752, -186048, 868608, -753984, 403776, -857088],
  [-207744, -476160, 938112, 5376, 856320, -271488, -126720, 78720, -1081344, 1798848, 3000000, -192384, 47616, 58176, 260352, 397248, 860736, -826368],
  [-69120, -3840, -778752, 49152, 322560, 171264, -193536, 49152, 108288, 67968, -192384, 446976, 110592, -111744, 78336, -28800, -77184, -32256],
  [-125952, -79872, -314880, 125952, 155136, 61440, -27648, 3072, 454656, 202752, 47616, 110592, 450048, -202752, 451584, -342528, -293376, -12288],
  [141696, 16896, 302976, -225024, -71424, 62592, 80640, 5760, -419328, -186048, 58176, -111744, -202752, 785088, -361728, 360000, 197568, -18432],
  [-253440, -141312, -746496, 529920, 179712, 158208, 110592, 205824, -27648, 868608, 260352, 78336, 451584, -361728, 1663488, -1587456, 39168, -179712],
  [263040, 13056, 794496, -478464, 235776, -139392, -301824, -164736, -142080, -753984, 397248, -28800, -342528, 360000, -1587456, 2241984, 43584, 227328],
  [1152, -77568, 11904, -134400, -51456, -109440, 89856, 306048, -585984, 403776, 860736, -77184, -293376, 197568, 39168, 43584, 725952, -319488],
  [145920, 136704, -371712, 13824, -413184, 59904, 18432, -58368, 536064, -857088, -826368, -32256, -12288, -18432, -179712, 227328, -319488, 440832]]

theorem amb_156k0 : x2KeyMult 0 blk_156k0 0 * x2KeyMult 0 blk_156k0 1 * x2KeyMult 0 blk_156k0 2 = 440 := by
  decide +kernel

theorem chk_156k0 : ∀ c < x2KeySize 0 blk_156k0, ∀ c' < x2KeySize 0 blk_156k0,
    x2TgtNum 72 6 blk_156k0 (x2JAll.getD (x2KeyGlobal 0 blk_156k0) []) c c' = (t8_156k0.getD c []).getD c' 0 := by
  decide +kernel

theorem tgt_156k0 : x2Target x2DataConcrete blk_156k0 =
    Matrix.of fun (c c' : x2Col 0 blk_156k0) => (((t8_156k0.getD c []).getD c' 0 : ℤ) : ℚ) / 8 :=
  x2Target_eq_lit x2DataConcrete blk_156k0 72 6 _ (fun c c' => (t8_156k0.getD c []).getD c' 0)
    (x2Target_eq_of_check x2DataConcrete blk_156k0 72 6 _ (by norm_num) (x2JAll_length_h blk_156k0)
      (x2ImageCols_concrete blk_156k0) (by rw [amb_156k0]; norm_num) (by rw [amb_156k0]; norm_num)) chk_156k0

/-- h block `222-2`. -/
def blk_222k2 : x2Key 0 := ⟨60, by decide⟩

/-- `T8 = Jᵀ (M ⊗ M ⊗ M) J` of block `222-2`. -/
def t8_222k2 : List (List ℤ) := [
  [58368, 46080],
  [46080, 181248]]

theorem amb_222k2 : x2KeyMult 0 blk_222k2 0 * x2KeyMult 0 blk_222k2 1 * x2KeyMult 0 blk_222k2 2 = 125 := by
  decide +kernel

theorem chk_222k2 : ∀ c < x2KeySize 0 blk_222k2, ∀ c' < x2KeySize 0 blk_222k2,
    x2TgtNum 72 5 blk_222k2 (x2JAll.getD (x2KeyGlobal 0 blk_222k2) []) c c' = (t8_222k2.getD c []).getD c' 0 := by
  decide +kernel

theorem tgt_222k2 : x2Target x2DataConcrete blk_222k2 =
    Matrix.of fun (c c' : x2Col 0 blk_222k2) => (((t8_222k2.getD c []).getD c' 0 : ℤ) : ℚ) / 8 :=
  x2Target_eq_lit x2DataConcrete blk_222k2 72 5 _ (fun c c' => (t8_222k2.getD c []).getD c' 0)
    (x2Target_eq_of_check x2DataConcrete blk_222k2 72 5 _ (by norm_num) (x2JAll_length_h blk_222k2)
      (x2ImageCols_concrete blk_222k2) (by rw [amb_222k2]; norm_num) (by rw [amb_222k2]; norm_num)) chk_222k2

/-- h block `224-1`. -/
def blk_224k1 : x2Key 0 := ⟨64, by decide⟩

/-- `T8 = Jᵀ (M ⊗ M ⊗ M) J` of block `224-1`. -/
def t8_224k1 : List (List ℤ) := [
  [1280, -7936, 3072, -1536, 12928, 2304, 384],
  [-7936, 141824, 67584, -31488, -78080, 32256, 75264],
  [3072, 67584, 66048, -1536, -7680, 29184, -3072],
  [-1536, -31488, -1536, -23808, -3072, -8448, 30720],
  [12928, -78080, -7680, -3072, 85184, 16128, 7104],
  [2304, 32256, 29184, -8448, 16128, 33792, -3072],
  [384, 75264, -3072, 30720, 7104, -3072, -58944]]

theorem amb_224k1 : x2KeyMult 0 blk_224k1 0 * x2KeyMult 0 blk_224k1 1 * x2KeyMult 0 blk_224k1 2 = 375 := by
  decide +kernel

theorem chk_224k1 : ∀ c < x2KeySize 0 blk_224k1, ∀ c' < x2KeySize 0 blk_224k1,
    x2TgtNum 72 5 blk_224k1 (x2JAll.getD (x2KeyGlobal 0 blk_224k1) []) c c' = (t8_224k1.getD c []).getD c' 0 := by
  decide +kernel

theorem tgt_224k1 : x2Target x2DataConcrete blk_224k1 =
    Matrix.of fun (c c' : x2Col 0 blk_224k1) => (((t8_224k1.getD c []).getD c' 0 : ℤ) : ℚ) / 8 :=
  x2Target_eq_lit x2DataConcrete blk_224k1 72 5 _ (fun c c' => (t8_224k1.getD c []).getD c' 0)
    (x2Target_eq_of_check x2DataConcrete blk_224k1 72 5 _ (by norm_num) (x2JAll_length_h blk_224k1)
      (x2ImageCols_concrete blk_224k1) (by rw [amb_224k1]; norm_num) (by rw [amb_224k1]; norm_num)) chk_224k1

/-- h block `226-1`. -/
def blk_226k1 : x2Key 0 := ⟨68, by decide⟩

/-- `T8 = Jᵀ (M ⊗ M ⊗ M) J` of block `226-1`. -/
def t8_226k1 : List (List ℤ) := [
  [372736, 86016, 0, 86016, 172032],
  [86016, -114688, -6144, 86016, 49152],
  [0, -6144, 28672, 77824, -10240],
  [86016, 86016, 77824, 28672, 8192],
  [172032, 49152, -10240, 8192, 77824]]

theorem amb_226k1 : x2KeyMult 0 blk_226k1 0 * x2KeyMult 0 blk_226k1 1 * x2KeyMult 0 blk_226k1 2 = 275 := by
  decide +kernel

theorem chk_226k1 : ∀ c < x2KeySize 0 blk_226k1, ∀ c' < x2KeySize 0 blk_226k1,
    x2TgtNum 72 5 blk_226k1 (x2JAll.getD (x2KeyGlobal 0 blk_226k1) []) c c' = (t8_226k1.getD c []).getD c' 0 := by
  decide +kernel

theorem tgt_226k1 : x2Target x2DataConcrete blk_226k1 =
    Matrix.of fun (c c' : x2Col 0 blk_226k1) => (((t8_226k1.getD c []).getD c' 0 : ℤ) : ℚ) / 8 :=
  x2Target_eq_lit x2DataConcrete blk_226k1 72 5 _ (fun c c' => (t8_226k1.getD c []).getD c' 0)
    (x2Target_eq_of_check x2DataConcrete blk_226k1 72 5 _ (by norm_num) (x2JAll_length_h blk_226k1)
      (x2ImageCols_concrete blk_226k1) (by rw [amb_226k1]; norm_num) (by rw [amb_226k1]; norm_num)) chk_226k1

/-- h block `235-0`. -/
def blk_235k0 : x2Key 0 := ⟨72, by decide⟩

/-- `T8 = Jᵀ (M ⊗ M ⊗ M) J` of block `235-0`. -/
def t8_235k0 : List (List ℤ) := [
  [215808, -48384, -182016, -117504, -240768, -261504, 67968, 330624, 88704, 2304],
  [-48384, 33024, 66816, 46080, -51840, 97920, -33408, -123264, -77184, 96768],
  [-182016, 66816, 840960, 258048, 180864, 358272, 125568, -415872, -291456, 322560],
  [-117504, 46080, 258048, 211968, -288000, 308736, -80640, -392832, -237312, 216576],
  [-240768, -51840, 180864, -288000, 1435392, -94464, 63360, 199296, 334080, -772992],
  [-261504, 97920, 358272, 308736, -94464, 1158912, -339840, -517248, -223488, 351360],
  [67968, -33408, 125568, -80640, 63360, -339840, 562176, 327168, 79488, 203904],
  [330624, -123264, -415872, -392832, 199296, -517248, 327168, 742464, 464256, -270720],
  [88704, -77184, -291456, -237312, 334080, -223488, 79488, 464256, 403200, -351360],
  [2304, 96768, 322560, 216576, -772992, 351360, 203904, -270720, -351360, 817920]]

theorem amb_235k0 : x2KeyMult 0 blk_235k0 0 * x2KeyMult 0 blk_235k0 1 * x2KeyMult 0 blk_235k0 2 = 250 := by
  decide +kernel

theorem chk_235k0 : ∀ c < x2KeySize 0 blk_235k0, ∀ c' < x2KeySize 0 blk_235k0,
    x2TgtNum 72 5 blk_235k0 (x2JAll.getD (x2KeyGlobal 0 blk_235k0) []) c c' = (t8_235k0.getD c []).getD c' 0 := by
  decide +kernel

theorem tgt_235k0 : x2Target x2DataConcrete blk_235k0 =
    Matrix.of fun (c c' : x2Col 0 blk_235k0) => (((t8_235k0.getD c []).getD c' 0 : ℤ) : ℚ) / 8 :=
  x2Target_eq_lit x2DataConcrete blk_235k0 72 5 _ (fun c c' => (t8_235k0.getD c []).getD c' 0)
    (x2Target_eq_of_check x2DataConcrete blk_235k0 72 5 _ (by norm_num) (x2JAll_length_h blk_235k0)
      (x2ImageCols_concrete blk_235k0) (by rw [amb_235k0]; norm_num) (by rw [amb_235k0]; norm_num)) chk_235k0

/-- h block `255-0`. -/
def blk_255k0 : x2Key 0 := ⟨78, by decide⟩

/-- `T8 = Jᵀ (M ⊗ M ⊗ M) J` of block `255-0`. -/
def t8_255k0 : List (List ℤ) := [
  [3015936, -1465344, -1974528, -3299328, -1340928, 195840, -471552, 821760, -10368, 405504, 62208, -1617408, -1324032],
  [-1465344, 6824448, 4796928, -1133568, 1511424, 2027520, -254976, -1675776, 253440, -4078080, -485376, 4363776, 668160],
  [-1974528, 4796928, 5234688, 6308352, 2947584, -1198080, 1787904, 105984, -11520, 368640, -342528, 884736, 1274880],
  [-3299328, -1133568, 6308352, 8469504, 2211840, -990720, 3323904, 1035264, -202752, 105984, 792576, -1631232, 2411520],
  [-1340928, 1511424, 2947584, 2211840, 1886208, -215040, 651264, -132096, 156672, -267264, -38912, 1188864, 535040],
  [195840, 2027520, -1198080, -990720, -215040, 3663360, -253440, -483840, -11520, -1797120, 399360, 1198080, -92160],
  [-471552, -254976, 1787904, 3323904, 651264, -253440, 1166336, 449536, -39936, 195072, 353280, -430080, 565760],
  [821760, -1675776, 105984, 1035264, -132096, -483840, 449536, 605696, -93696, 371712, 147456, -1482240, -51200],
  [-10368, 253440, -11520, -202752, 156672, -11520, -39936, -93696, 77184, -119808, -66816, 271872, -11520],
  [405504, -4078080, 368640, 105984, -267264, -1797120, 195072, 371712, -119808, 1737216, 231936, -2363904, -46080],
  [62208, -485376, -342528, 792576, -38912, 399360, 353280, 147456, -66816, 231936, 154112, -365568, 103424],
  [-1617408, 4363776, 884736, -1631232, 1188864, 1198080, -430080, -1482240, 271872, -2363904, -365568, 4889088, 322560],
  [-1324032, 668160, 1274880, 2411520, 535040, -92160, 565760, -51200, -11520, -46080, 103424, 322560, 693760]]

theorem amb_255k0 : x2KeyMult 0 blk_255k0 0 * x2KeyMult 0 blk_255k0 1 * x2KeyMult 0 blk_255k0 2 = 500 := by
  decide +kernel

theorem chk_255k0 : ∀ c < x2KeySize 0 blk_255k0, ∀ c' < x2KeySize 0 blk_255k0,
    x2TgtNum 72 6 blk_255k0 (x2JAll.getD (x2KeyGlobal 0 blk_255k0) []) c c' = (t8_255k0.getD c []).getD c' 0 := by
  decide +kernel

theorem tgt_255k0 : x2Target x2DataConcrete blk_255k0 =
    Matrix.of fun (c c' : x2Col 0 blk_255k0) => (((t8_255k0.getD c []).getD c' 0 : ℤ) : ℚ) / 8 :=
  x2Target_eq_lit x2DataConcrete blk_255k0 72 6 _ (fun c c' => (t8_255k0.getD c []).getD c' 0)
    (x2Target_eq_of_check x2DataConcrete blk_255k0 72 6 _ (by norm_num) (x2JAll_length_h blk_255k0)
      (x2ImageCols_concrete blk_255k0) (by rw [amb_255k0]; norm_num) (by rw [amb_255k0]; norm_num)) chk_255k0

/-- h block `266-1`. -/
def blk_266k1 : x2Key 0 := ⟨82, by decide⟩

/-- `T8 = Jᵀ (M ⊗ M ⊗ M) J` of block `266-1`. -/
def t8_266k1 : List (List ℤ) := [
  [123904, -18432, 294912, 13312, -61440, -408576, 144384, -98304, 95232],
  [-18432, 53248, -24576, -59392, 172032, -67584, 79872, -811008, 276480],
  [294912, -24576, 4349952, -307200, -1327104, 2138112, -1916928, 1130496, 491520],
  [13312, -59392, -307200, 72704, 73728, 70656, -248832, 749568, -408576],
  [-61440, 172032, -1327104, 73728, 2654208, -847872, 2617344, -3858432, 1167360],
  [-408576, -67584, 2138112, 70656, -847872, 6792192, 193536, 2998272, -297984],
  [144384, 79872, -1916928, -248832, 2617344, 193536, -64512, -3268608, -408576],
  [-98304, -811008, 1130496, 749568, -3858432, 2998272, -3268608, 14843904, -3440640],
  [95232, 276480, 491520, -408576, 1167360, -297984, -408576, -3440640, 1336320]]

theorem amb_266k1 : x2KeyMult 0 blk_266k1 0 * x2KeyMult 0 blk_266k1 1 * x2KeyMult 0 blk_266k1 2 = 605 := by
  decide +kernel

theorem chk_266k1 : ∀ c < x2KeySize 0 blk_266k1, ∀ c' < x2KeySize 0 blk_266k1,
    x2TgtNum 72 6 blk_266k1 (x2JAll.getD (x2KeyGlobal 0 blk_266k1) []) c c' = (t8_266k1.getD c []).getD c' 0 := by
  decide +kernel

theorem tgt_266k1 : x2Target x2DataConcrete blk_266k1 =
    Matrix.of fun (c c' : x2Col 0 blk_266k1) => (((t8_266k1.getD c []).getD c' 0 : ℤ) : ℚ) / 8 :=
  x2Target_eq_lit x2DataConcrete blk_266k1 72 6 _ (fun c c' => (t8_266k1.getD c []).getD c' 0)
    (x2Target_eq_of_check x2DataConcrete blk_266k1 72 6 _ (by norm_num) (x2JAll_length_h blk_266k1)
      (x2ImageCols_concrete blk_266k1) (by rw [amb_266k1]; norm_num) (by rw [amb_266k1]; norm_num)) chk_266k1

/-- h block `334-1`. -/
def blk_334k1 : x2Key 0 := ⟨86, by decide⟩

/-- `T8 = Jᵀ (M ⊗ M ⊗ M) J` of block `334-1`. -/
def t8_334k1 : List (List ℤ) := [
  [2875392, 649728, 566784, 165888, -221184, -691200],
  [649728, 1797120, -670464, -20736, -525312, -304128],
  [566784, -670464, 566784, 145152, 179712, -96768],
  [165888, -20736, 145152, 720576, 15552, 108864],
  [-221184, -525312, 179712, 15552, 278208, 12096],
  [-691200, -304128, -96768, 108864, 12096, 319680]]

theorem amb_334k1 : x2KeyMult 0 blk_334k1 0 * x2KeyMult 0 blk_334k1 1 * x2KeyMult 0 blk_334k1 2 = 375 := by
  decide +kernel

theorem chk_334k1 : ∀ c < x2KeySize 0 blk_334k1, ∀ c' < x2KeySize 0 blk_334k1,
    x2TgtNum 72 5 blk_334k1 (x2JAll.getD (x2KeyGlobal 0 blk_334k1) []) c c' = (t8_334k1.getD c []).getD c' 0 := by
  decide +kernel

theorem tgt_334k1 : x2Target x2DataConcrete blk_334k1 =
    Matrix.of fun (c c' : x2Col 0 blk_334k1) => (((t8_334k1.getD c []).getD c' 0 : ℤ) : ℚ) / 8 :=
  x2Target_eq_lit x2DataConcrete blk_334k1 72 5 _ (fun c c' => (t8_334k1.getD c []).getD c' 0)
    (x2Target_eq_of_check x2DataConcrete blk_334k1 72 5 _ (by norm_num) (x2JAll_length_h blk_334k1)
      (x2ImageCols_concrete blk_334k1) (by rw [amb_334k1]; norm_num) (by rw [amb_334k1]; norm_num)) chk_334k1

/-- h block `336-1`. -/
def blk_336k1 : x2Key 0 := ⟨90, by decide⟩

/-- `T8 = Jᵀ (M ⊗ M ⊗ M) J` of block `336-1`. -/
def t8_336k1 : List (List ℤ) := [
  [16896, -165888, 27648, -55296, -12288],
  [-165888, 5640192, -718848, 1161216, 405504],
  [27648, -718848, 497664, 442368, -36864],
  [-55296, 1161216, 442368, 1327104, 73728],
  [-12288, 405504, -36864, 73728, 36864]]

theorem amb_336k1 : x2KeyMult 0 blk_336k1 0 * x2KeyMult 0 blk_336k1 1 * x2KeyMult 0 blk_336k1 2 = 275 := by
  decide +kernel

theorem chk_336k1 : ∀ c < x2KeySize 0 blk_336k1, ∀ c' < x2KeySize 0 blk_336k1,
    x2TgtNum 72 5 blk_336k1 (x2JAll.getD (x2KeyGlobal 0 blk_336k1) []) c c' = (t8_336k1.getD c []).getD c' 0 := by
  decide +kernel

theorem tgt_336k1 : x2Target x2DataConcrete blk_336k1 =
    Matrix.of fun (c c' : x2Col 0 blk_336k1) => (((t8_336k1.getD c []).getD c' 0 : ℤ) : ℚ) / 8 :=
  x2Target_eq_lit x2DataConcrete blk_336k1 72 5 _ (fun c c' => (t8_336k1.getD c []).getD c' 0)
    (x2Target_eq_of_check x2DataConcrete blk_336k1 72 5 _ (by norm_num) (x2JAll_length_h blk_336k1)
      (x2ImageCols_concrete blk_336k1) (by rw [amb_336k1]; norm_num) (by rw [amb_336k1]; norm_num)) chk_336k1

/-- h block `355-1`. -/
def blk_355k1 : x2Key 0 := ⟨96, by decide⟩

/-- `T8 = Jᵀ (M ⊗ M ⊗ M) J` of block `355-1`. -/
def t8_355k1 : List (List ℤ) := [
  [739584, 64512, 698112, -103680, -92160, 260352, -103680, -48384, 177408],
  [64512, 548352, 158976, 103680, 219648, 278016, -357120, -1405440, -102912],
  [698112, 158976, 5273856, -656640, -622080, 781056, -1486080, -940032, 324864],
  [-103680, 103680, -656640, 483840, 264960, 288000, 138240, -656640, 57600],
  [-92160, 219648, -622080, 264960, -285696, 207360, -34560, -336384, 64512],
  [260352, 278016, 781056, 288000, 207360, 650496, -495360, -1642752, 94464],
  [-103680, -357120, -1486080, 138240, -34560, -495360, 967680, 1486080, -34560],
  [-48384, -1405440, -940032, -656640, -336384, -1642752, 1486080, 5971968, -11520],
  [177408, -102912, 324864, 57600, 64512, 94464, -34560, -11520, 76032]]

theorem amb_355k1 : x2KeyMult 0 blk_355k1 0 * x2KeyMult 0 blk_355k1 1 * x2KeyMult 0 blk_355k1 2 = 500 := by
  decide +kernel

theorem chk_355k1 : ∀ c < x2KeySize 0 blk_355k1, ∀ c' < x2KeySize 0 blk_355k1,
    x2TgtNum 72 6 blk_355k1 (x2JAll.getD (x2KeyGlobal 0 blk_355k1) []) c c' = (t8_355k1.getD c []).getD c' 0 := by
  decide +kernel

theorem tgt_355k1 : x2Target x2DataConcrete blk_355k1 =
    Matrix.of fun (c c' : x2Col 0 blk_355k1) => (((t8_355k1.getD c []).getD c' 0 : ℤ) : ℚ) / 8 :=
  x2Target_eq_lit x2DataConcrete blk_355k1 72 6 _ (fun c c' => (t8_355k1.getD c []).getD c' 0)
    (x2Target_eq_of_check x2DataConcrete blk_355k1 72 6 _ (by norm_num) (x2JAll_length_h blk_355k1)
      (x2ImageCols_concrete blk_355k1) (by rw [amb_355k1]; norm_num) (by rw [amb_355k1]; norm_num)) chk_355k1

end ThreeCopyQutritWerner.X2.Tgt
