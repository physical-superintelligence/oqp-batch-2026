module

public import ThreeCopyQutritWerner.CertificateX2OutputConcrete
public import ThreeCopyQutritWerner.CertificateX2OutputSplit

@[expose] public section


/-! Output stage: targets `x2Target x2DataConcrete b = T8 / 8` of h blocks
004-0, 013-0, 022-0, 026-0, 036-0, 046-0, 066-0, 112-0, 114-0, 116-0, 123-0, 133-0, 136-0, 146-0, 166-0, 223-0, 225-0, 233-0, 236-0, 255-1, 333-0, 335-0, 345-0, 356-0. The kernel computes `Jᵀ (M ⊗ M ⊗ M) J` from the images of CertificateX2Images and the local tables
of CertificateX2Reduced (W = 72). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThreeCopyQutritWerner.X2.Tgt

/-- h block `004-0`. -/
def blk_004k0 : x2Key 0 := ⟨1, by decide⟩

/-- `T8 = Jᵀ (M ⊗ M ⊗ M) J` of block `004-0`. -/
def t8_004k0 : List (List ℤ) := [
  [192]]

theorem amb_004k0 : x2KeyMult 0 blk_004k0 0 * x2KeyMult 0 blk_004k0 1 * x2KeyMult 0 blk_004k0 2 = 15 := by
  decide +kernel

theorem chk_004k0 : ∀ c < x2KeySize 0 blk_004k0, ∀ c' < x2KeySize 0 blk_004k0,
    x2TgtNum 72 1 blk_004k0 (x2JAll.getD (x2KeyGlobal 0 blk_004k0) []) c c' = (t8_004k0.getD c []).getD c' 0 := by
  decide +kernel

theorem tgt_004k0 : x2Target x2DataConcrete blk_004k0 =
    Matrix.of fun (c c' : x2Col 0 blk_004k0) => (((t8_004k0.getD c []).getD c' 0 : ℤ) : ℚ) / 8 :=
  x2Target_eq_lit x2DataConcrete blk_004k0 72 1 _ (fun c c' => (t8_004k0.getD c []).getD c' 0)
    (x2Target_eq_of_check x2DataConcrete blk_004k0 72 1 _ (by norm_num) (x2JAll_length_h blk_004k0)
      (x2ImageCols_concrete blk_004k0) (by rw [amb_004k0]; norm_num) (by rw [amb_004k0]; norm_num)) chk_004k0

/-- h block `013-0`. -/
def blk_013k0 : x2Key 0 := ⟨5, by decide⟩

/-- `T8 = Jᵀ (M ⊗ M ⊗ M) J` of block `013-0`. -/
def t8_013k0 : List (List ℤ) := [
  [3840]]

theorem amb_013k0 : x2KeyMult 0 blk_013k0 0 * x2KeyMult 0 blk_013k0 1 * x2KeyMult 0 blk_013k0 2 = 20 := by
  decide +kernel

theorem chk_013k0 : ∀ c < x2KeySize 0 blk_013k0, ∀ c' < x2KeySize 0 blk_013k0,
    x2TgtNum 72 2 blk_013k0 (x2JAll.getD (x2KeyGlobal 0 blk_013k0) []) c c' = (t8_013k0.getD c []).getD c' 0 := by
  decide +kernel

theorem tgt_013k0 : x2Target x2DataConcrete blk_013k0 =
    Matrix.of fun (c c' : x2Col 0 blk_013k0) => (((t8_013k0.getD c []).getD c' 0 : ℤ) : ℚ) / 8 :=
  x2Target_eq_lit x2DataConcrete blk_013k0 72 2 _ (fun c c' => (t8_013k0.getD c []).getD c' 0)
    (x2Target_eq_of_check x2DataConcrete blk_013k0 72 2 _ (by norm_num) (x2JAll_length_h blk_013k0)
      (x2ImageCols_concrete blk_013k0) (by rw [amb_013k0]; norm_num) (by rw [amb_013k0]; norm_num)) chk_013k0

/-- h block `022-0`. -/
def blk_022k0 : x2Key 0 := ⟨9, by decide⟩

/-- `T8 = Jᵀ (M ⊗ M ⊗ M) J` of block `022-0`. -/
def t8_022k0 : List (List ℤ) := [
  [256]]

theorem amb_022k0 : x2KeyMult 0 blk_022k0 0 * x2KeyMult 0 blk_022k0 1 * x2KeyMult 0 blk_022k0 2 = 25 := by
  decide +kernel

theorem chk_022k0 : ∀ c < x2KeySize 0 blk_022k0, ∀ c' < x2KeySize 0 blk_022k0,
    x2TgtNum 72 3 blk_022k0 (x2JAll.getD (x2KeyGlobal 0 blk_022k0) []) c c' = (t8_022k0.getD c []).getD c' 0 := by
  decide +kernel

theorem tgt_022k0 : x2Target x2DataConcrete blk_022k0 =
    Matrix.of fun (c c' : x2Col 0 blk_022k0) => (((t8_022k0.getD c []).getD c' 0 : ℤ) : ℚ) / 8 :=
  x2Target_eq_lit x2DataConcrete blk_022k0 72 3 _ (fun c c' => (t8_022k0.getD c []).getD c' 0)
    (x2Target_eq_of_check x2DataConcrete blk_022k0 72 3 _ (by norm_num) (x2JAll_length_h blk_022k0)
      (x2ImageCols_concrete blk_022k0) (by rw [amb_022k0]; norm_num) (by rw [amb_022k0]; norm_num)) chk_022k0

/-- h block `026-0`. -/
def blk_026k0 : x2Key 0 := ⟨13, by decide⟩

/-- `T8 = Jᵀ (M ⊗ M ⊗ M) J` of block `026-0`. -/
def t8_026k0 : List (List ℤ) := [
  [2560, -5120],
  [-5120, 5120]]

theorem amb_026k0 : x2KeyMult 0 blk_026k0 0 * x2KeyMult 0 blk_026k0 1 * x2KeyMult 0 blk_026k0 2 = 55 := by
  decide +kernel

theorem chk_026k0 : ∀ c < x2KeySize 0 blk_026k0, ∀ c' < x2KeySize 0 blk_026k0,
    x2TgtNum 72 3 blk_026k0 (x2JAll.getD (x2KeyGlobal 0 blk_026k0) []) c c' = (t8_026k0.getD c []).getD c' 0 := by
  decide +kernel

theorem tgt_026k0 : x2Target x2DataConcrete blk_026k0 =
    Matrix.of fun (c c' : x2Col 0 blk_026k0) => (((t8_026k0.getD c []).getD c' 0 : ℤ) : ℚ) / 8 :=
  x2Target_eq_lit x2DataConcrete blk_026k0 72 3 _ (fun c c' => (t8_026k0.getD c []).getD c' 0)
    (x2Target_eq_of_check x2DataConcrete blk_026k0 72 3 _ (by norm_num) (x2JAll_length_h blk_026k0)
      (x2ImageCols_concrete blk_026k0) (by rw [amb_026k0]; norm_num) (by rw [amb_026k0]; norm_num)) chk_026k0

/-- h block `036-0`. -/
def blk_036k0 : x2Key 0 := ⟨17, by decide⟩

/-- `T8 = Jᵀ (M ⊗ M ⊗ M) J` of block `036-0`. -/
def t8_036k0 : List (List ℤ) := [
  [7680, -6144],
  [-6144, 6144]]

theorem amb_036k0 : x2KeyMult 0 blk_036k0 0 * x2KeyMult 0 blk_036k0 1 * x2KeyMult 0 blk_036k0 2 = 55 := by
  decide +kernel

theorem chk_036k0 : ∀ c < x2KeySize 0 blk_036k0, ∀ c' < x2KeySize 0 blk_036k0,
    x2TgtNum 72 3 blk_036k0 (x2JAll.getD (x2KeyGlobal 0 blk_036k0) []) c c' = (t8_036k0.getD c []).getD c' 0 := by
  decide +kernel

theorem tgt_036k0 : x2Target x2DataConcrete blk_036k0 =
    Matrix.of fun (c c' : x2Col 0 blk_036k0) => (((t8_036k0.getD c []).getD c' 0 : ℤ) : ℚ) / 8 :=
  x2Target_eq_lit x2DataConcrete blk_036k0 72 3 _ (fun c c' => (t8_036k0.getD c []).getD c' 0)
    (x2Target_eq_of_check x2DataConcrete blk_036k0 72 3 _ (by norm_num) (x2JAll_length_h blk_036k0)
      (x2ImageCols_concrete blk_036k0) (by rw [amb_036k0]; norm_num) (by rw [amb_036k0]; norm_num)) chk_036k0

/-- h block `046-0`. -/
def blk_046k0 : x2Key 0 := ⟨21, by decide⟩

/-- `T8 = Jᵀ (M ⊗ M ⊗ M) J` of block `046-0`. -/
def t8_046k0 : List (List ℤ) := [
  [58112, 512, -41728, 1536, -50688, -2048, -33280],
  [512, 18944, -16384, -26112, 25344, -20480, -7936],
  [-41728, -16384, 84224, 33792, 52992, 10240, 62720],
  [1536, -26112, 33792, 104960, -45312, 26624, 21760],
  [-50688, 25344, 52992, -45312, 61824, -23040, 31872],
  [-2048, -20480, 10240, 26624, -23040, 20224, 512],
  [-33280, -7936, 62720, 21760, 31872, 512, 56704]]

theorem amb_046k0 : x2KeyMult 0 blk_046k0 0 * x2KeyMult 0 blk_046k0 1 * x2KeyMult 0 blk_046k0 2 = 165 := by
  decide +kernel

theorem chk_046k0 : ∀ c < x2KeySize 0 blk_046k0, ∀ c' < x2KeySize 0 blk_046k0,
    x2TgtNum 72 4 blk_046k0 (x2JAll.getD (x2KeyGlobal 0 blk_046k0) []) c c' = (t8_046k0.getD c []).getD c' 0 := by
  decide +kernel

theorem tgt_046k0 : x2Target x2DataConcrete blk_046k0 =
    Matrix.of fun (c c' : x2Col 0 blk_046k0) => (((t8_046k0.getD c []).getD c' 0 : ℤ) : ℚ) / 8 :=
  x2Target_eq_lit x2DataConcrete blk_046k0 72 4 _ (fun c c' => (t8_046k0.getD c []).getD c' 0)
    (x2Target_eq_of_check x2DataConcrete blk_046k0 72 4 _ (by norm_num) (x2JAll_length_h blk_046k0)
      (x2ImageCols_concrete blk_046k0) (by rw [amb_046k0]; norm_num) (by rw [amb_046k0]; norm_num)) chk_046k0

/-- h block `066-0`. -/
def blk_066k0 : x2Key 0 := ⟨25, by decide⟩

/-- `T8 = Jᵀ (M ⊗ M ⊗ M) J` of block `066-0`. -/
def t8_066k0 : List (List ℤ) := [
  [1617920, -204800, 184320, -675840],
  [-204800, 25600, 34816, 73728],
  [184320, 34816, 65536, -241664],
  [-675840, 73728, -241664, 438272]]

theorem amb_066k0 : x2KeyMult 0 blk_066k0 0 * x2KeyMult 0 blk_066k0 1 * x2KeyMult 0 blk_066k0 2 = 121 := by
  decide +kernel

theorem chk_066k0 : ∀ c < x2KeySize 0 blk_066k0, ∀ c' < x2KeySize 0 blk_066k0,
    x2TgtNum 72 4 blk_066k0 (x2JAll.getD (x2KeyGlobal 0 blk_066k0) []) c c' = (t8_066k0.getD c []).getD c' 0 := by
  decide +kernel

theorem tgt_066k0 : x2Target x2DataConcrete blk_066k0 =
    Matrix.of fun (c c' : x2Col 0 blk_066k0) => (((t8_066k0.getD c []).getD c' 0 : ℤ) : ℚ) / 8 :=
  x2Target_eq_lit x2DataConcrete blk_066k0 72 4 _ (fun c c' => (t8_066k0.getD c []).getD c' 0)
    (x2Target_eq_of_check x2DataConcrete blk_066k0 72 4 _ (by norm_num) (x2JAll_length_h blk_066k0)
      (x2ImageCols_concrete blk_066k0) (by rw [amb_066k0]; norm_num) (by rw [amb_066k0]; norm_num)) chk_066k0

/-- h block `112-0`. -/
def blk_112k0 : x2Key 0 := ⟨29, by decide⟩

/-- `T8 = Jᵀ (M ⊗ M ⊗ M) J` of block `112-0`. -/
def t8_112k0 : List (List ℤ) := [
  [14848, -2304, 5632],
  [-2304, 512, -256],
  [5632, -256, 4608]]

theorem amb_112k0 : x2KeyMult 0 blk_112k0 0 * x2KeyMult 0 blk_112k0 1 * x2KeyMult 0 blk_112k0 2 = 80 := by
  decide +kernel

theorem chk_112k0 : ∀ c < x2KeySize 0 blk_112k0, ∀ c' < x2KeySize 0 blk_112k0,
    x2TgtNum 72 4 blk_112k0 (x2JAll.getD (x2KeyGlobal 0 blk_112k0) []) c c' = (t8_112k0.getD c []).getD c' 0 := by
  decide +kernel

theorem tgt_112k0 : x2Target x2DataConcrete blk_112k0 =
    Matrix.of fun (c c' : x2Col 0 blk_112k0) => (((t8_112k0.getD c []).getD c' 0 : ℤ) : ℚ) / 8 :=
  x2Target_eq_lit x2DataConcrete blk_112k0 72 4 _ (fun c c' => (t8_112k0.getD c []).getD c' 0)
    (x2Target_eq_of_check x2DataConcrete blk_112k0 72 4 _ (by norm_num) (x2JAll_length_h blk_112k0)
      (x2ImageCols_concrete blk_112k0) (by rw [amb_112k0]; norm_num) (by rw [amb_112k0]; norm_num)) chk_112k0

/-- h block `114-0`. -/
def blk_114k0 : x2Key 0 := ⟨33, by decide⟩

/-- `T8 = Jᵀ (M ⊗ M ⊗ M) J` of block `114-0`. -/
def t8_114k0 : List (List ℤ) := [
  [4992, -5504, -9280, 14336, -3520, 14336, 14848],
  [-5504, 30080, 12608, -31232, -2880, -28160, -30720],
  [-9280, 12608, 30240, -22400, 10976, -25472, -22400],
  [14336, -31232, -22400, 63104, -9600, 59520, 59776],
  [-3520, -2880, 10976, -9600, 12832, -9600, -9088],
  [14336, -28160, -25472, 59520, -9600, 68224, 59264],
  [14848, -30720, -22400, 59776, -9088, 59264, 61056]]

theorem amb_114k0 : x2KeyMult 0 blk_114k0 0 * x2KeyMult 0 blk_114k0 1 * x2KeyMult 0 blk_114k0 2 = 240 := by
  decide +kernel

theorem chk_114k0 : ∀ c < x2KeySize 0 blk_114k0, ∀ c' < x2KeySize 0 blk_114k0,
    x2TgtNum 72 4 blk_114k0 (x2JAll.getD (x2KeyGlobal 0 blk_114k0) []) c c' = (t8_114k0.getD c []).getD c' 0 := by
  decide +kernel

theorem tgt_114k0 : x2Target x2DataConcrete blk_114k0 =
    Matrix.of fun (c c' : x2Col 0 blk_114k0) => (((t8_114k0.getD c []).getD c' 0 : ℤ) : ℚ) / 8 :=
  x2Target_eq_lit x2DataConcrete blk_114k0 72 4 _ (fun c c' => (t8_114k0.getD c []).getD c' 0)
    (x2Target_eq_of_check x2DataConcrete blk_114k0 72 4 _ (by norm_num) (x2JAll_length_h blk_114k0)
      (x2ImageCols_concrete blk_114k0) (by rw [amb_114k0]; norm_num) (by rw [amb_114k0]; norm_num)) chk_114k0

/-- h block `116-0`. -/
def blk_116k0 : x2Key 0 := ⟨37, by decide⟩

/-- `T8 = Jᵀ (M ⊗ M ⊗ M) J` of block `116-0`. -/
def t8_116k0 : List (List ℤ) := [
  [1044480, -153600, -860160, 122880],
  [-153600, 65280, -7680, -66048],
  [-860160, -7680, 952320, -21504],
  [122880, -66048, -21504, 58368]]

theorem amb_116k0 : x2KeyMult 0 blk_116k0 0 * x2KeyMult 0 blk_116k0 1 * x2KeyMult 0 blk_116k0 2 = 176 := by
  decide +kernel

theorem chk_116k0 : ∀ c < x2KeySize 0 blk_116k0, ∀ c' < x2KeySize 0 blk_116k0,
    x2TgtNum 72 4 blk_116k0 (x2JAll.getD (x2KeyGlobal 0 blk_116k0) []) c c' = (t8_116k0.getD c []).getD c' 0 := by
  decide +kernel

theorem tgt_116k0 : x2Target x2DataConcrete blk_116k0 =
    Matrix.of fun (c c' : x2Col 0 blk_116k0) => (((t8_116k0.getD c []).getD c' 0 : ℤ) : ℚ) / 8 :=
  x2Target_eq_lit x2DataConcrete blk_116k0 72 4 _ (fun c c' => (t8_116k0.getD c []).getD c' 0)
    (x2Target_eq_of_check x2DataConcrete blk_116k0 72 4 _ (by norm_num) (x2JAll_length_h blk_116k0)
      (x2ImageCols_concrete blk_116k0) (by rw [amb_116k0]; norm_num) (by rw [amb_116k0]; norm_num)) chk_116k0

/-- h block `123-0`. -/
def blk_123k0 : x2Key 0 := ⟨41, by decide⟩

/-- `T8 = Jᵀ (M ⊗ M ⊗ M) J` of block `123-0`. -/
def t8_123k0 : List (List ℤ) := [
  [18176, -15744, 13824, 17664, 10624],
  [-15744, 21504, -16896, -22656, -4608],
  [13824, -16896, 30720, 16896, 7680],
  [17664, -22656, 16896, 28416, 7296],
  [10624, -4608, 7680, 7296, 9728]]

theorem amb_123k0 : x2KeyMult 0 blk_123k0 0 * x2KeyMult 0 blk_123k0 1 * x2KeyMult 0 blk_123k0 2 = 100 := by
  decide +kernel

theorem chk_123k0 : ∀ c < x2KeySize 0 blk_123k0, ∀ c' < x2KeySize 0 blk_123k0,
    x2TgtNum 72 5 blk_123k0 (x2JAll.getD (x2KeyGlobal 0 blk_123k0) []) c c' = (t8_123k0.getD c []).getD c' 0 := by
  decide +kernel

theorem tgt_123k0 : x2Target x2DataConcrete blk_123k0 =
    Matrix.of fun (c c' : x2Col 0 blk_123k0) => (((t8_123k0.getD c []).getD c' 0 : ℤ) : ℚ) / 8 :=
  x2Target_eq_lit x2DataConcrete blk_123k0 72 5 _ (fun c c' => (t8_123k0.getD c []).getD c' 0)
    (x2Target_eq_of_check x2DataConcrete blk_123k0 72 5 _ (by norm_num) (x2JAll_length_h blk_123k0)
      (x2ImageCols_concrete blk_123k0) (by rw [amb_123k0]; norm_num) (by rw [amb_123k0]; norm_num)) chk_123k0

/-- h block `133-0`. -/
def blk_133k0 : x2Key 0 := ⟨45, by decide⟩

/-- `T8 = Jᵀ (M ⊗ M ⊗ M) J` of block `133-0`. -/
def t8_133k0 : List (List ℤ) := [
  [6144, -1536, 4608],
  [-1536, 26880, -6912],
  [4608, -6912, 20736]]

theorem amb_133k0 : x2KeyMult 0 blk_133k0 0 * x2KeyMult 0 blk_133k0 1 * x2KeyMult 0 blk_133k0 2 = 100 := by
  decide +kernel

theorem chk_133k0 : ∀ c < x2KeySize 0 blk_133k0, ∀ c' < x2KeySize 0 blk_133k0,
    x2TgtNum 72 5 blk_133k0 (x2JAll.getD (x2KeyGlobal 0 blk_133k0) []) c c' = (t8_133k0.getD c []).getD c' 0 := by
  decide +kernel

theorem tgt_133k0 : x2Target x2DataConcrete blk_133k0 =
    Matrix.of fun (c c' : x2Col 0 blk_133k0) => (((t8_133k0.getD c []).getD c' 0 : ℤ) : ℚ) / 8 :=
  x2Target_eq_lit x2DataConcrete blk_133k0 72 5 _ (fun c c' => (t8_133k0.getD c []).getD c' 0)
    (x2Target_eq_of_check x2DataConcrete blk_133k0 72 5 _ (by norm_num) (x2JAll_length_h blk_133k0)
      (x2ImageCols_concrete blk_133k0) (by rw [amb_133k0]; norm_num) (by rw [amb_133k0]; norm_num)) chk_133k0

/-- h block `136-0`. -/
def blk_136k0 : x2Key 0 := ⟨49, by decide⟩

/-- `T8 = Jᵀ (M ⊗ M ⊗ M) J` of block `136-0`. -/
def t8_136k0 : List (List ℤ) := [
  [141312, -35328, 41472, -46080, -69120, -39168, -147456, -71424, 6912],
  [-35328, 210432, 156672, 69120, -115200, 129792, -239616, -301824, 191232],
  [41472, 156672, 520704, 18432, -129024, 67584, -175104, -175104, 202752],
  [-46080, 69120, 18432, 48384, -2304, 71424, -87552, 2304, 29952],
  [-69120, -115200, -129024, -2304, 165888, -59904, 216576, 230400, -184320],
  [-39168, 129792, 67584, 71424, -59904, 126976, -188928, -92160, 94464],
  [-147456, -239616, -175104, -87552, 216576, -188928, 764928, 336384, -207360],
  [-71424, -301824, -175104, 2304, 230400, -92160, 336384, 654336, -380160],
  [6912, 191232, 202752, 29952, -184320, 94464, -207360, -380160, 267264]]

theorem amb_136k0 : x2KeyMult 0 blk_136k0 0 * x2KeyMult 0 blk_136k0 1 * x2KeyMult 0 blk_136k0 2 = 220 := by
  decide +kernel

theorem chk_136k0 : ∀ c < x2KeySize 0 blk_136k0, ∀ c' < x2KeySize 0 blk_136k0,
    x2TgtNum 72 5 blk_136k0 (x2JAll.getD (x2KeyGlobal 0 blk_136k0) []) c c' = (t8_136k0.getD c []).getD c' 0 := by
  decide +kernel

theorem tgt_136k0 : x2Target x2DataConcrete blk_136k0 =
    Matrix.of fun (c c' : x2Col 0 blk_136k0) => (((t8_136k0.getD c []).getD c' 0 : ℤ) : ℚ) / 8 :=
  x2Target_eq_lit x2DataConcrete blk_136k0 72 5 _ (fun c c' => (t8_136k0.getD c []).getD c' 0)
    (x2Target_eq_of_check x2DataConcrete blk_136k0 72 5 _ (by norm_num) (x2JAll_length_h blk_136k0)
      (x2ImageCols_concrete blk_136k0) (by rw [amb_136k0]; norm_num) (by rw [amb_136k0]; norm_num)) chk_136k0

/-- h block `146-0`. -/
def blk_146k0 : x2Key 0 := ⟨53, by decide⟩

/-- `T8 = Jᵀ (M ⊗ M ⊗ M) J` of block `146-0`. -/
def t8_146k0 : List (List ℤ) := [
  [2521344, -742656, 53760, -450432, -490752, -727488, 1031424, 172608, 422016, 716352, 505152, 83328, 252672, -198912, -54144, 9792, -233472, 54720, 404928, -795264, -580800, 33600, 16896, 79296, -888960, 69312, 357504],
  [-742656, 1717248, -34560, -144000, -301824, 14400, -478464, 312384, -970368, -1512384, 671040, -168576, 14592, 314112, -150912, -342720, 113664, 123840, 192960, 283776, -12480, -110784, 199680, -2112, -129408, -39744, 690816],
  [53760, -34560, 167424, -11520, 72192, 64128, -23040, -34176, 4608, -16512, 118656, 158976, -272640, 148224, -161280, 84864, -69888, -220032, 21888, 22272, 51072, -35712, 34560, -75648, 78336, -30592, 186624],
  [-450432, -144000, -11520, 1766016, 364800, 315264, 240768, -689664, 549504, -40320, -662016, 689280, 185088, 72192, 116352, 844416, 647424, 89088, -696960, -87552, 209280, 387840, -614016, 158208, 498816, 23040, -431232],
  [-490752, -301824, 72192, 364800, 284928, 116736, -140544, -43008, 106752, 207360, -187392, 150528, -284160, 109824, 6144, 188928, -52224, -211200, -314880, 129024, 204288, -94464, -158976, 9984, 298752, -40704, -279552],
  [-727488, 14400, 64128, 315264, 116736, 1214304, -315072, -586464, -56832, 66528, -434784, 407424, 14208, -170112, -112512, 590688, 344064, 98400, -348000, 210240, 175200, 169632, -32832, -119328, 382848, 29664, 272256],
  [1031424, -478464, -23040, 240768, -140544, -315072, 1247232, -118464, 375168, 452928, -36288, -32640, 597504, -241152, -160128, 226368, 217344, 45504, -106560, -782976, -93120, 227904, -157440, 274368, -193920, 135360, 151680],
  [172608, 312384, -34176, -689664, -43008, -586464, -118464, 1174752, -537984, -276576, 361056, -304128, -91776, -112512, -75264, -594144, -403200, -105312, 263904, 95424, -120288, -428448, 194496, -13536, -560640, -28896, -30720],
  [422016, -970368, 4608, 549504, 106752, -56832, 375168, -537984, 1073280, 1076736, -626304, 107136, 409344, -39936, 5760, 350208, 433920, 51072, -202752, -178176, 31488, 224640, -363648, 44928, 266880, 66432, -550272],
  [716352, -1512384, -16512, -40320, 207360, 66528, 452928, -276576, 1076736, 1395552, -412128, 170112, 126336, -339072, 42624, 391392, -102912, -60192, -190944, -253632, 58080, 73248, -266304, 61536, 202368, 47712, -571776],
  [505152, 671040, 118656, -662016, -187392, -434784, -36288, 361056, -626304, -412128, 826848, -123648, -356736, 384, 74496, -447840, -468480, -139488, 331872, -60480, 26016, -179232, 552384, -182112, -298752, -23136, 455424],
  [83328, -168576, 158976, 689280, 150528, 407424, -32640, -304128, 107136, 170112, -123648, 934272, -235776, 1536, -92544, 620928, 278784, 144384, -395904, -102144, 263040, 61440, -158592, -209664, 187008, 12288, 53376],
  [252672, 14592, -272640, 185088, -284160, 14208, 597504, -91776, 409344, 126336, -356736, -235776, 1518336, -200448, -39936, -33408, 582144, 483456, -55680, 47616, -187776, 306816, -88320, 398976, -126720, 200832, -80640],
  [-198912, 314112, 148224, 72192, 109824, -170112, -241152, -112512, -39936, -339072, 384, 1536, -200448, 594432, -164352, -111744, -39936, -272256, 54912, 312576, -10368, -29568, -5376, 87936, 101376, -63360, 69120],
  [-54144, -150912, -161280, 116352, 6144, -112512, -160128, -75264, 5760, 42624, 74496, -92544, -39936, -164352, 418176, -35712, -188928, 228864, 86400, -89856, -31872, 29184, -40320, -79872, 72576, -10752, -414336],
  [9792, -342720, 84864, 844416, 188928, 590688, 226368, -594144, 350208, 391392, -447840, 620928, -33408, -111744, -35712, 1012320, 324864, 118368, -436320, -303552, 97632, 176544, -334656, -140832, 220032, 45024, -111744],
  [-233472, 113664, -69888, 647424, -52224, 344064, 217344, -403200, 433920, -102912, -468480, 278784, 582144, -39936, -188928, 324864, 710400, 307968, -288000, -99840, 38400, 202752, -318720, 147456, 284160, 72960, 40704],
  [54720, 123840, -220032, 89088, -211200, 98400, 45504, -105312, 51072, -60192, -139488, 144384, 483456, -272256, 228864, 118368, 307968, 729312, 125088, -319680, -97440, 173088, -179136, -110496, -70656, 87648, -268800],
  [404928, 192960, 21888, -696960, -314880, -348000, -106560, 263904, -202752, -190944, 331872, -395904, -55680, 54912, 86400, -436320, -288000, 125088, 560736, -37440, -352608, -35232, 196416, -74208, -302976, 4896, 126336],
  [-795264, 283776, 22272, -87552, 129024, 210240, -782976, 95424, -178176, -253632, -60480, -102144, 47616, 312576, -89856, -303552, -99840, -319680, -37440, 1034112, 119616, -71232, 216192, 43584, 121344, -60864, 19968],
  [-580800, -12480, 51072, 209280, 204288, 175200, -93120, -120288, 31488, 58080, 26016, 263040, -187776, -10368, -31872, 97632, 38400, -97440, -352608, 119616, 461664, -20064, 7872, -42528, 514944, -17184, -26496],
  [33600, -110784, -35712, 387840, -94464, 169632, 227904, -428448, 224640, 73248, -179232, 61440, 306816, -29568, 29184, 176544, 202752, 173088, -35232, -71232, -20064, 326112, -85056, 65184, 168960, 51360, 40704],
  [16896, 199680, 34560, -614016, -158976, -32832, -157440, 194496, -363648, -266304, 552384, -158592, -88320, -5376, -40320, -334656, -318720, -179136, 196416, 216192, 7872, -85056, 463872, -101568, -119424, -23232, 442752],
  [79296, -2112, -75648, 158208, 9984, -119328, 274368, -13536, 44928, 61536, -182112, -209664, 398976, 87936, -79872, -140832, 147456, -110496, -74208, 43584, -42528, 65184, -101568, 343008, -92928, 26592, -12288],
  [-888960, -129408, 78336, 498816, 298752, 382848, -193920, -560640, 266880, 202368, -298752, 187008, -126720, 101376, 72576, 220032, 284160, -70656, -302976, 121344, 514944, 168960, -119424, -92928, 812928, -15360, -249984],
  [69312, -39744, -30592, 23040, -40704, 29664, 135360, -28896, 66432, 47712, -23136, 12288, 200832, -63360, -10752, 45024, 72960, 87648, 4896, -60864, -17184, 51360, -23232, 26592, -15360, 31200, -1536],
  [357504, 690816, 186624, -431232, -279552, 272256, 151680, -30720, -550272, -571776, 455424, 53376, -80640, 69120, -414336, -111744, 40704, -268800, 126336, 19968, -26496, 40704, 442752, -12288, -249984, -1536, 1166976]]

theorem amb_146k0 : x2KeyMult 0 blk_146k0 0 * x2KeyMult 0 blk_146k0 1 * x2KeyMult 0 blk_146k0 2 = 660 := by
  decide +kernel

theorem chk_146k0 : ∀ c < x2KeySize 0 blk_146k0, ∀ c' < x2KeySize 0 blk_146k0,
    x2TgtNum 72 6 blk_146k0 (x2JAll.getD (x2KeyGlobal 0 blk_146k0) []) c c' = (t8_146k0.getD c []).getD c' 0 := by
  decide +kernel

theorem tgt_146k0 : x2Target x2DataConcrete blk_146k0 =
    Matrix.of fun (c c' : x2Col 0 blk_146k0) => (((t8_146k0.getD c []).getD c' 0 : ℤ) : ℚ) / 8 :=
  x2Target_eq_lit x2DataConcrete blk_146k0 72 6 _ (fun c c' => (t8_146k0.getD c []).getD c' 0)
    (x2Target_eq_of_check x2DataConcrete blk_146k0 72 6 _ (by norm_num) (x2JAll_length_h blk_146k0)
      (x2ImageCols_concrete blk_146k0) (by rw [amb_146k0]; norm_num) (by rw [amb_146k0]; norm_num)) chk_146k0

/-- h block `166-0`. -/
def blk_166k0 : x2Key 0 := ⟨57, by decide⟩

/-- `T8 = Jᵀ (M ⊗ M ⊗ M) J` of block `166-0`. -/
def t8_166k0 : List (List ℤ) := [
  [7231488, -1007616, -964608, -7305216, -5090304, -6014976, 285696, 1044480, -832512, 98304, -12288, -30720],
  [-1007616, 7655424, 73728, 12288, 3545088, 3551232, -141312, -7286784, 890880, 2199552, -270336, -602112],
  [-964608, 73728, 1136640, 1124352, -156672, 2562048, -289792, -147456, 734208, 602112, -458752, 178176],
  [-7305216, 12288, 1124352, 15562752, 8315904, 9000960, -1963008, -3624960, 3763200, -6144000, -307200, 3164160],
  [-5090304, 3545088, -156672, 8315904, 8581632, 3449856, -920064, -3028992, 720384, -491520, 958464, 162816],
  [-6014976, 3551232, 2562048, 9000960, 3449856, 10106880, -402432, -4177920, 887808, 122880, -1105920, 436224],
  [285696, -141312, -289792, -1963008, -920064, -402432, 655872, 731136, -1242624, 417792, 139264, -814080],
  [1044480, -7286784, -147456, -3624960, -3028992, -4177920, 731136, 8724480, -854016, 86016, 688128, 233472],
  [-832512, 890880, 734208, 3763200, 720384, 887808, -1242624, -854016, 4121088, -12288, -847872, 3204096],
  [98304, 2199552, 602112, -6144000, -491520, 122880, 417792, 86016, -12288, 5554176, 86016, -2371584],
  [-12288, -270336, -458752, -307200, 958464, -1105920, 139264, 688128, -847872, 86016, 540672, -638976],
  [-30720, -602112, 178176, 3164160, 162816, 436224, -814080, 233472, 3204096, -2371584, -638976, 2955264]]

theorem amb_166k0 : x2KeyMult 0 blk_166k0 0 * x2KeyMult 0 blk_166k0 1 * x2KeyMult 0 blk_166k0 2 = 484 := by
  decide +kernel

theorem chk_166k0 : ∀ c < x2KeySize 0 blk_166k0, ∀ c' < x2KeySize 0 blk_166k0,
    x2TgtNum 72 6 blk_166k0 (x2JAll.getD (x2KeyGlobal 0 blk_166k0) []) c c' = (t8_166k0.getD c []).getD c' 0 := by
  decide +kernel

theorem tgt_166k0 : x2Target x2DataConcrete blk_166k0 =
    Matrix.of fun (c c' : x2Col 0 blk_166k0) => (((t8_166k0.getD c []).getD c' 0 : ℤ) : ℚ) / 8 :=
  x2Target_eq_lit x2DataConcrete blk_166k0 72 6 _ (fun c c' => (t8_166k0.getD c []).getD c' 0)
    (x2Target_eq_of_check x2DataConcrete blk_166k0 72 6 _ (by norm_num) (x2JAll_length_h blk_166k0)
      (x2ImageCols_concrete blk_166k0) (by rw [amb_166k0]; norm_num) (by rw [amb_166k0]; norm_num)) chk_166k0

/-- h block `223-0`. -/
def blk_223k0 : x2Key 0 := ⟨61, by decide⟩

/-- `T8 = Jᵀ (M ⊗ M ⊗ M) J` of block `223-0`. -/
def t8_223k0 : List (List ℤ) := [
  [35840, 8704, -28928, 67584, 17152],
  [8704, 34304, -22528, 19968, 9728],
  [-28928, -22528, 37376, -54528, -24064],
  [67584, 19968, -54528, 138240, 25344],
  [17152, 9728, -24064, 25344, 12288]]

theorem amb_223k0 : x2KeyMult 0 blk_223k0 0 * x2KeyMult 0 blk_223k0 1 * x2KeyMult 0 blk_223k0 2 = 125 := by
  decide +kernel

theorem chk_223k0 : ∀ c < x2KeySize 0 blk_223k0, ∀ c' < x2KeySize 0 blk_223k0,
    x2TgtNum 72 5 blk_223k0 (x2JAll.getD (x2KeyGlobal 0 blk_223k0) []) c c' = (t8_223k0.getD c []).getD c' 0 := by
  decide +kernel

theorem tgt_223k0 : x2Target x2DataConcrete blk_223k0 =
    Matrix.of fun (c c' : x2Col 0 blk_223k0) => (((t8_223k0.getD c []).getD c' 0 : ℤ) : ℚ) / 8 :=
  x2Target_eq_lit x2DataConcrete blk_223k0 72 5 _ (fun c c' => (t8_223k0.getD c []).getD c' 0)
    (x2Target_eq_of_check x2DataConcrete blk_223k0 72 5 _ (by norm_num) (x2JAll_length_h blk_223k0)
      (x2ImageCols_concrete blk_223k0) (by rw [amb_223k0]; norm_num) (by rw [amb_223k0]; norm_num)) chk_223k0

/-- h block `225-0`. -/
def blk_225k0 : x2Key 0 := ⟨65, by decide⟩

/-- `T8 = Jᵀ (M ⊗ M ⊗ M) J` of block `225-0`. -/
def t8_225k0 : List (List ℤ) := [
  [1526016, -353280, -21504, 456960, -546816, -79872, 1555968, 74496],
  [-353280, 26112, -32256, -542208, -190464, 84480, -528384, -173568],
  [-21504, -32256, 2304, 6144, -29184, -33792, -7680, -76800],
  [456960, -542208, 6144, 590592, -666624, -15360, 1261056, -123648],
  [-546816, -190464, -29184, -666624, 943104, 609792, -1413120, 614400],
  [-79872, 84480, -33792, -15360, 609792, 413184, -1536, 576768],
  [1555968, -528384, -7680, 1261056, -1413120, -1536, 2214912, -185856],
  [74496, -173568, -76800, -123648, 614400, 576768, -185856, 582528]]

theorem amb_225k0 : x2KeyMult 0 blk_225k0 0 * x2KeyMult 0 blk_225k0 1 * x2KeyMult 0 blk_225k0 2 = 250 := by
  decide +kernel

theorem chk_225k0 : ∀ c < x2KeySize 0 blk_225k0, ∀ c' < x2KeySize 0 blk_225k0,
    x2TgtNum 72 5 blk_225k0 (x2JAll.getD (x2KeyGlobal 0 blk_225k0) []) c c' = (t8_225k0.getD c []).getD c' 0 := by
  decide +kernel

theorem tgt_225k0 : x2Target x2DataConcrete blk_225k0 =
    Matrix.of fun (c c' : x2Col 0 blk_225k0) => (((t8_225k0.getD c []).getD c' 0 : ℤ) : ℚ) / 8 :=
  x2Target_eq_lit x2DataConcrete blk_225k0 72 5 _ (fun c c' => (t8_225k0.getD c []).getD c' 0)
    (x2Target_eq_of_check x2DataConcrete blk_225k0 72 5 _ (by norm_num) (x2JAll_length_h blk_225k0)
      (x2ImageCols_concrete blk_225k0) (by rw [amb_225k0]; norm_num) (by rw [amb_225k0]; norm_num)) chk_225k0

/-- h block `233-0`. -/
def blk_233k0 : x2Key 0 := ⟨69, by decide⟩

/-- `T8 = Jᵀ (M ⊗ M ⊗ M) J` of block `233-0`. -/
def t8_233k0 : List (List ℤ) := [
  [46080, 32256, 4608, 18432],
  [32256, 172032, -53760, 10752],
  [4608, -53760, 24576, -7680],
  [18432, 10752, -7680, 52224]]

theorem amb_233k0 : x2KeyMult 0 blk_233k0 0 * x2KeyMult 0 blk_233k0 1 * x2KeyMult 0 blk_233k0 2 = 125 := by
  decide +kernel

theorem chk_233k0 : ∀ c < x2KeySize 0 blk_233k0, ∀ c' < x2KeySize 0 blk_233k0,
    x2TgtNum 72 5 blk_233k0 (x2JAll.getD (x2KeyGlobal 0 blk_233k0) []) c c' = (t8_233k0.getD c []).getD c' 0 := by
  decide +kernel

theorem tgt_233k0 : x2Target x2DataConcrete blk_233k0 =
    Matrix.of fun (c c' : x2Col 0 blk_233k0) => (((t8_233k0.getD c []).getD c' 0 : ℤ) : ℚ) / 8 :=
  x2Target_eq_lit x2DataConcrete blk_233k0 72 5 _ (fun c c' => (t8_233k0.getD c []).getD c' 0)
    (x2Target_eq_of_check x2DataConcrete blk_233k0 72 5 _ (by norm_num) (x2JAll_length_h blk_233k0)
      (x2ImageCols_concrete blk_233k0) (by rw [amb_233k0]; norm_num) (by rw [amb_233k0]; norm_num)) chk_233k0

/-- h block `236-0`. -/
def blk_236k0 : x2Key 0 := ⟨73, by decide⟩

/-- `T8 = Jᵀ (M ⊗ M ⊗ M) J` of block `236-0`. -/
def t8_236k0 : List (List ℤ) := [
  [273408, -41472, 24576, 26112, -129024, 124416, -741888, -225792, -46080, -50688, -211968],
  [-41472, 1216512, 69120, 124416, -396288, 442368, 253440, -529920, -921600, -387072, 175104],
  [24576, 69120, 61440, 16896, -92160, 55296, -41472, -41472, -64512, -161280, 13824],
  [26112, 124416, 16896, 45056, -101376, 121344, -92160, -70656, -82944, -38400, 70656],
  [-129024, -396288, -92160, -101376, 276480, -211968, 262656, 170496, 322560, 248832, -32256],
  [124416, 442368, 55296, 121344, -211968, 329472, -39168, -352512, -170496, -59904, 119808],
  [-741888, 253440, -41472, -92160, 262656, -39168, 1910016, 661248, 18432, 78336, 640512],
  [-225792, -529920, -41472, -70656, 170496, -352512, 661248, 887040, 470016, 142848, 340992],
  [-46080, -921600, -64512, -82944, 322560, -170496, 18432, 470016, 838656, 331776, -23040],
  [-50688, -387072, -161280, -38400, 248832, -59904, 78336, 142848, 331776, 635904, 4608],
  [-211968, 175104, 13824, 70656, -32256, 119808, 640512, 340992, -23040, 4608, 465408]]

theorem amb_236k0 : x2KeyMult 0 blk_236k0 0 * x2KeyMult 0 blk_236k0 1 * x2KeyMult 0 blk_236k0 2 = 275 := by
  decide +kernel

theorem chk_236k0 : ∀ c < x2KeySize 0 blk_236k0, ∀ c' < x2KeySize 0 blk_236k0,
    x2TgtNum 72 5 blk_236k0 (x2JAll.getD (x2KeyGlobal 0 blk_236k0) []) c c' = (t8_236k0.getD c []).getD c' 0 := by
  decide +kernel

theorem tgt_236k0 : x2Target x2DataConcrete blk_236k0 =
    Matrix.of fun (c c' : x2Col 0 blk_236k0) => (((t8_236k0.getD c []).getD c' 0 : ℤ) : ℚ) / 8 :=
  x2Target_eq_lit x2DataConcrete blk_236k0 72 5 _ (fun c c' => (t8_236k0.getD c []).getD c' 0)
    (x2Target_eq_of_check x2DataConcrete blk_236k0 72 5 _ (by norm_num) (x2JAll_length_h blk_236k0)
      (x2ImageCols_concrete blk_236k0) (by rw [amb_236k0]; norm_num) (by rw [amb_236k0]; norm_num)) chk_236k0

/-- h block `255-1`. -/
def blk_255k1 : x2Key 0 := ⟨79, by decide⟩

/-- `T8 = Jᵀ (M ⊗ M ⊗ M) J` of block `255-1`. -/
def t8_255k1 : List (List ℤ) := [
  [8022528, -304128, 313344, -500736, -6345216, 1096704, -350208],
  [-304128, 27648, 1536, 37376, 178176, -36864, 27648],
  [313344, 1536, 18432, 26112, -281088, 10752, -267264],
  [-500736, 37376, 26112, 131072, 532992, -76288, -105984],
  [-6345216, 178176, -281088, 532992, 6077952, -872448, -336384],
  [1096704, -36864, 10752, -76288, -872448, 248832, 285696],
  [-350208, 27648, -267264, -105984, -336384, 285696, 211968]]

theorem amb_255k1 : x2KeyMult 0 blk_255k1 0 * x2KeyMult 0 blk_255k1 1 * x2KeyMult 0 blk_255k1 2 = 500 := by
  decide +kernel

theorem chk_255k1 : ∀ c < x2KeySize 0 blk_255k1, ∀ c' < x2KeySize 0 blk_255k1,
    x2TgtNum 72 6 blk_255k1 (x2JAll.getD (x2KeyGlobal 0 blk_255k1) []) c c' = (t8_255k1.getD c []).getD c' 0 := by
  decide +kernel

theorem tgt_255k1 : x2Target x2DataConcrete blk_255k1 =
    Matrix.of fun (c c' : x2Col 0 blk_255k1) => (((t8_255k1.getD c []).getD c' 0 : ℤ) : ℚ) / 8 :=
  x2Target_eq_lit x2DataConcrete blk_255k1 72 6 _ (fun c c' => (t8_255k1.getD c []).getD c' 0)
    (x2Target_eq_of_check x2DataConcrete blk_255k1 72 6 _ (by norm_num) (x2JAll_length_h blk_255k1)
      (x2ImageCols_concrete blk_255k1) (by rw [amb_255k1]; norm_num) (by rw [amb_255k1]; norm_num)) chk_255k1

/-- h block `333-0`. -/
def blk_333k0 : x2Key 0 := ⟨83, by decide⟩

/-- `T8 = Jᵀ (M ⊗ M ⊗ M) J` of block `333-0`. -/
def t8_333k0 : List (List ℤ) := [
  [20736, 20736],
  [20736, 34560]]

theorem amb_333k0 : x2KeyMult 0 blk_333k0 0 * x2KeyMult 0 blk_333k0 1 * x2KeyMult 0 blk_333k0 2 = 125 := by
  decide +kernel

theorem chk_333k0 : ∀ c < x2KeySize 0 blk_333k0, ∀ c' < x2KeySize 0 blk_333k0,
    x2TgtNum 72 5 blk_333k0 (x2JAll.getD (x2KeyGlobal 0 blk_333k0) []) c c' = (t8_333k0.getD c []).getD c' 0 := by
  decide +kernel

theorem tgt_333k0 : x2Target x2DataConcrete blk_333k0 =
    Matrix.of fun (c c' : x2Col 0 blk_333k0) => (((t8_333k0.getD c []).getD c' 0 : ℤ) : ℚ) / 8 :=
  x2Target_eq_lit x2DataConcrete blk_333k0 72 5 _ (fun c c' => (t8_333k0.getD c []).getD c' 0)
    (x2Target_eq_of_check x2DataConcrete blk_333k0 72 5 _ (by norm_num) (x2JAll_length_h blk_333k0)
      (x2ImageCols_concrete blk_333k0) (by rw [amb_333k0]; norm_num) (by rw [amb_333k0]; norm_num)) chk_333k0

/-- h block `335-0`. -/
def blk_335k0 : x2Key 0 := ⟨87, by decide⟩

/-- `T8 = Jᵀ (M ⊗ M ⊗ M) J` of block `335-0`. -/
def t8_335k0 : List (List ℤ) := [
  [100224, -228096, 63360, -41472, 20736, -114048, 69120],
  [-228096, -297216, -23040, -93312, -82944, 41472, -276480],
  [63360, -23040, 196992, -16128, -4608, -86400, -66816],
  [-41472, -93312, -16128, 121728, 23424, 59904, -176256],
  [20736, -82944, -4608, 23424, 28416, -18432, -20736],
  [-114048, 41472, -86400, 59904, -18432, 141696, -103680],
  [69120, -276480, -66816, -176256, -20736, -103680, 269568]]

theorem amb_335k0 : x2KeyMult 0 blk_335k0 0 * x2KeyMult 0 blk_335k0 1 * x2KeyMult 0 blk_335k0 2 = 250 := by
  decide +kernel

theorem chk_335k0 : ∀ c < x2KeySize 0 blk_335k0, ∀ c' < x2KeySize 0 blk_335k0,
    x2TgtNum 72 5 blk_335k0 (x2JAll.getD (x2KeyGlobal 0 blk_335k0) []) c c' = (t8_335k0.getD c []).getD c' 0 := by
  decide +kernel

theorem tgt_335k0 : x2Target x2DataConcrete blk_335k0 =
    Matrix.of fun (c c' : x2Col 0 blk_335k0) => (((t8_335k0.getD c []).getD c' 0 : ℤ) : ℚ) / 8 :=
  x2Target_eq_lit x2DataConcrete blk_335k0 72 5 _ (fun c c' => (t8_335k0.getD c []).getD c' 0)
    (x2Target_eq_of_check x2DataConcrete blk_335k0 72 5 _ (by norm_num) (x2JAll_length_h blk_335k0)
      (x2ImageCols_concrete blk_335k0) (by rw [amb_335k0]; norm_num) (by rw [amb_335k0]; norm_num)) chk_335k0

/-- h block `345-0`. -/
def blk_345k0 : x2Key 0 := ⟨93, by decide⟩

/-- `T8 = Jᵀ (M ⊗ M ⊗ M) J` of block `345-0`. -/
def t8_345k0 : List (List ℤ) := [
  [2204928, 1021824, -1183104, -545472, -952128, -405504, 149184, 836928, -702720, -435456, 449280, -914112, 4608, -1056384, -509184, -417024, -173952, -85824, -755136, -721728, 1009728, 177408, -53568, 1551744, -1044288, 807552, -471168, -739584, -652608, -71232, 278784],
  [1021824, 2970432, -1126080, -418752, -1416960, -608832, 255168, 861696, -756864, -688896, 509184, -808704, -475200, -733824, 106560, -149760, -704448, 92160, 110016, -787392, 1635840, 524160, -262656, 510336, -1286208, 552384, -124416, 6336, -538560, 61248, 267840],
  [-1183104, -1126080, 2214720, -22464, 1126656, 380160, 245376, -819072, 188928, 131904, 115200, 597888, 372672, 1624320, 160704, -70848, -116352, 70272, 56448, -111168, -965952, -114048, -362880, -396864, 721152, -331776, -72000, 75456, 134208, -18048, -97920],
  [-545472, -418752, -22464, 1954944, 31104, -115200, 119808, -9792, 1152, 192384, -301248, 273024, -80640, 232704, 36864, 372672, -138240, 0, -61056, 89856, 377280, 384768, 108864, -189504, 13824, -329472, 25344, 963648, -86400, 172224, 44352],
  [-952128, -1416960, 1126656, 31104, 2416320, 608256, 131328, -633024, 740736, -157248, 262656, 1184832, -133056, 988992, -226368, -330048, -265536, 321408, 19008, 114048, -1166400, 0, -233280, -793152, 665856, -599616, 701568, -191808, 948096, -21312, -178560],
  [-405504, -608832, 380160, -115200, 608256, 1873728, -56448, 482688, 160128, 385920, 659520, 330048, 380736, 239616, 349632, 427968, -508032, 430272, 149760, -292032, -1075968, -347904, 134784, -548928, -117504, 28224, 82368, 4608, 307584, -23616, 268992],
  [149184, 255168, 245376, 119808, 131328, -56448, 436032, 161280, -88704, -184320, 286272, 323136, -179136, 163584, -80640, -244224, -513216, 226368, -67968, -482112, 384192, 256896, -188352, 187200, -131328, 78336, -213120, 72000, -108864, 23040, 42624],
  [836928, 861696, -819072, -9792, -633024, 482688, 161280, 1534464, -388224, 26496, 828864, -308736, -14976, -806400, -78912, 11520, -732096, 222912, -92160, -768960, 778176, -99072, -17280, 446400, -1187712, 302976, -102528, 66816, -57600, -33984, 259200],
  [-702720, -756864, 188928, 1152, 740736, 160128, -88704, -388224, 1516608, -27072, -74880, 373824, 20736, 243648, 365760, -35712, 179136, 119808, 270720, 17856, -499968, -32256, 50112, -700992, 398016, 234432, 511488, 27072, 929664, 768, -110016],
  [-435456, -688896, 131904, 192384, -157248, 385920, -184320, 26496, -27072, 1479168, 129600, 1728, 421056, 66816, 242496, 676800, -104832, -173952, 257472, 48960, -476352, -683136, 274752, -290304, -150912, -59904, 69696, 418176, 16128, -62016, -28800],
  [449280, 509184, 115200, -301248, 262656, 659520, 286272, 828864, -74880, 129600, 1356480, -6912, 259776, -21888, -327168, -237888, -933696, 536832, -62208, -1268928, 400320, -260352, 44928, 3456, -744192, 462528, 153216, -212544, 87552, -34176, 84096],
  [-914112, -808704, 597888, 273024, 1184832, 330048, 323136, -308736, 373824, 1728, -6912, 1434816, -96768, 626688, -428544, -271296, -137088, 406080, -157248, -224640, -616896, 0, -100224, -400896, 868608, -464832, 383616, 117504, 375552, 15552, -284544],
  [4608, -475200, 372672, -80640, -133056, 380736, -179136, -14976, 20736, 421056, 259776, -96768, 1256256, -161280, 80064, 180864, 177408, -131904, -56448, 122112, -123840, -327168, 136512, 94464, -198144, 4032, 27648, -28800, -12672, -76800, -15552],
  [-1056384, -733824, 1624320, 232704, 988992, 239616, 163584, -806400, 243648, 66816, -21888, 626688, -161280, 1381824, 135936, 36864, -110016, 165888, 214848, -10368, -506880, 81792, -3456, -631296, 866304, -401472, 147456, 130176, 220608, 24192, -183168],
  [-509184, 106560, 160704, 36864, -226368, 349632, -80640, -78912, 365760, 242496, -327168, -428544, 80064, 135936, 1180800, 643968, -6912, -134784, 490176, 262656, -286272, 184320, -72576, -326016, 141696, 74880, -263232, 225792, 177984, 16128, 263808],
  [-417024, -149760, -70848, 372672, -330048, 427968, -244224, 11520, -35712, 676800, -237888, -271296, 180864, 36864, 643968, 1177344, 88128, -184896, 372096, 314496, -337536, -125568, 345600, -396288, 0, -154368, -77184, 826560, -108864, 104256, 194112],
  [-173952, -704448, -116352, -138240, -265536, -508032, -513216, -732096, 179136, -104832, -933696, -137088, 177408, -110016, -6912, 88128, 1070208, -389376, -85248, 1354176, -342144, -31104, 70848, 33408, 605952, -158976, -141120, -197568, -139968, -8256, -212544],
  [-85824, 92160, 70272, 0, 321408, 430272, 226368, 222912, 119808, -173952, 536832, 406080, -131904, 165888, -134784, -184896, -389376, 510912, 68544, -391104, 100224, 169344, 5184, -211968, -13248, 91584, 16128, -109440, 106560, 55104, 80064],
  [-755136, 110016, 56448, -61056, 19008, 149760, -67968, -92160, 270720, 257472, -62208, -157248, -56448, 214848, 490176, 372096, -85248, 68544, 1064448, 158400, -138816, -28800, -39744, -639360, 344448, -48960, -168192, 77760, 288000, 116736, 173952],
  [-721728, -787392, -111168, 89856, 114048, -292032, -482112, -768960, 17856, 48960, -1268928, -224640, 122112, -10368, 262656, 314496, 1354176, -391104, 158400, 1544256, -682560, 110592, 115776, -172224, 966528, -316224, -42624, 40896, -19584, 10752, -70272],
  [1009728, 1635840, -965952, 377280, -1166400, -1075968, 384192, 778176, -499968, -476352, 400320, -616896, -123840, -506880, -286272, -337536, -342144, 100224, -138816, -682560, 1910016, 713088, -43200, 1082304, -908928, 512064, -296064, -33408, -506304, 78912, 294912],
  [177408, 524160, -114048, 384768, 0, -347904, 256896, -99072, -32256, -683136, -260352, 0, -327168, 81792, 184320, -125568, -31104, 169344, -28800, 110592, 713088, 1115136, -127872, 163584, 196992, 42624, -104832, -52992, -127872, 104832, 230400],
  [-53568, -262656, -362880, 108864, -233280, 134784, -188352, -17280, 50112, 274752, 44928, -100224, 136512, -3456, -72576, 345600, 70848, 5184, -39744, 115776, -43200, -127872, 684288, -31104, 34560, 44928, 58752, 145152, -58752, -10944, -13824],
  [1551744, 510336, -396864, -189504, -793152, -548928, 187200, 446400, -700992, -290304, 3456, -400896, 94464, -631296, -326016, -396288, 33408, -211968, -639360, -172224, 1082304, 163584, -31104, 1404864, -643392, 323712, -542016, -352512, -669888, -96576, 28224],
  [-1044288, -1286208, 721152, 13824, 665856, -117504, -131328, -1187712, 398016, -150912, -744192, 868608, -198144, 866304, 141696, 0, 605952, -13248, 344448, 966528, -908928, 196992, 34560, -643392, 1304640, -527040, 4608, -135936, 117504, 64128, -148032],
  [807552, 552384, -331776, -329472, -599616, 28224, 78336, 302976, 234432, -59904, 462528, -464832, 4032, -401472, 74880, -154368, -158976, 91584, -48960, -316224, 512064, 42624, 44928, 323712, -527040, 845568, -277056, -304704, -88128, -49536, 72000],
  [-471168, -124416, -72000, 25344, 701568, 82368, -213120, -102528, 511488, 69696, 153216, 383616, 27648, 147456, -263232, -77184, -141120, 16128, -168192, -42624, -296064, -104832, 58752, -542016, 4608, -277056, 870912, 23616, 532800, -44160, -158976],
  [-739584, 6336, 75456, 963648, -191808, 4608, 72000, 66816, 27072, 418176, -212544, 117504, -28800, 130176, 225792, 826560, -197568, -109440, 77760, 40896, -33408, -52992, 145152, -352512, -135936, -304704, 23616, 1276992, -24768, 113280, 1152],
  [-652608, -538560, 134208, -86400, 948096, 307584, -108864, -57600, 929664, 16128, 87552, 375552, -12672, 220608, 177984, -108864, -139968, 106560, 288000, -19584, -506304, -127872, -58752, -669888, 117504, -88128, 532800, -24768, 790272, -26688, -92160],
  [-71232, 61248, -18048, 172224, -21312, -23616, 23040, -33984, 768, -62016, -34176, 15552, -76800, 24192, 16128, 104256, -8256, 55104, 116736, 10752, 78912, 104832, -10944, -96576, 64128, -49536, -44160, 113280, -26688, 71552, 52608],
  [278784, 267840, -97920, 44352, -178560, 268992, 42624, 259200, -110016, -28800, 84096, -284544, -15552, -183168, 263808, 194112, -212544, 80064, 173952, -70272, 294912, 230400, -13824, 28224, -148032, 72000, -158976, 1152, -92160, 52608, 254592]]

theorem amb_345k0 : x2KeyMult 0 blk_345k0 0 * x2KeyMult 0 blk_345k0 1 * x2KeyMult 0 blk_345k0 2 = 750 := by
  decide +kernel

theorem chk_345k0 : ∀ c < x2KeySize 0 blk_345k0, ∀ c' < x2KeySize 0 blk_345k0,
    x2TgtNum 72 7 blk_345k0 (x2JAll.getD (x2KeyGlobal 0 blk_345k0) []) c c' = (t8_345k0.getD c []).getD c' 0 := by
  decide +kernel

theorem tgt_345k0 : x2Target x2DataConcrete blk_345k0 =
    Matrix.of fun (c c' : x2Col 0 blk_345k0) => (((t8_345k0.getD c []).getD c' 0 : ℤ) : ℚ) / 8 :=
  x2Target_eq_lit x2DataConcrete blk_345k0 72 7 _ (fun c c' => (t8_345k0.getD c []).getD c' 0)
    (x2Target_eq_of_check x2DataConcrete blk_345k0 72 7 _ (by norm_num) (x2JAll_length_h blk_345k0)
      (x2ImageCols_concrete blk_345k0) (by rw [amb_345k0]; norm_num) (by rw [amb_345k0]; norm_num)) chk_345k0

/-- h block `356-0`. -/
def blk_356k0 : x2Key 0 := ⟨97, by decide⟩

/-- `T8 = Jᵀ (M ⊗ M ⊗ M) J` of block `356-0`. -/
def t8_356k0 : List (List ℤ) := [
  [1064448, -331776, -2032128, 306432, -184320, 260352, -1029888, 1396224, 1327104, 442368, 387072, 124416, 622080, 414720, -131328, -1064448, 327168, 145152, -1741824, -525312, -1375488, 1575936, 442368],
  [-331776, 322560, 534528, -131328, -75264, -178944, 1177344, -506880, -198144, -129024, -529920, 253440, -179712, -599040, 145152, 235008, -434688, 149760, 728064, 193536, 693504, -774144, -990720],
  [-2032128, 534528, 10423296, -933120, 631296, -458496, -518400, -3442176, -2322432, -940032, 235008, -635904, -1022976, 2128896, -380160, 2474496, -69120, -1085184, 2820096, 2488320, 1969920, -1465344, -110592],
  [306432, -131328, -933120, 140928, -59136, 104064, -210816, 407808, 320256, 191232, 237312, 101376, 191232, 101376, -72576, -225792, 104448, 10368, -516096, -195840, -268416, 668160, 59904],
  [-184320, -75264, 631296, -59136, 861696, -31488, 158976, -1013760, -483840, -373248, 1175040, 18432, -548352, 248832, 200448, 516096, 304128, -62208, 96768, 373248, 246528, -156672, 36864],
  [260352, -178944, -458496, 104064, -31488, 197760, -722304, 490752, 251136, 89856, 357120, -359424, 223488, 552960, -86400, -391680, 190464, -137088, -580608, -145152, -466560, 442368, 612864],
  [-1029888, 1177344, -518400, -210816, 158976, -722304, 9539712, -2177280, -20736, -149760, -2089728, -838656, -421632, -4156416, 3037824, 1704960, -1603584, 1342080, 3096576, 490752, 3583872, -2608128, -4428288],
  [1396224, -506880, -3442176, 407808, -1013760, 490752, -2177280, 6732288, 2847744, 1866240, -1880064, -787968, 2004480, 967680, -1002240, -3483648, 258048, -1057536, -2985984, -1824768, -1320192, 428544, 2543616],
  [1327104, -198144, -2322432, 320256, -483840, 251136, -20736, 2847744, 4852224, 1423872, -1741824, -497664, 1658880, 248832, 960768, -1548288, -138240, 725760, -1658880, -1313280, -1375488, -193536, 677376],
  [442368, -129024, -940032, 191232, -373248, 89856, -149760, 1866240, 1423872, 3902976, -377856, 1294848, 663552, 755712, 214272, -1304064, -82944, 182016, -304128, -1009152, -103680, 64512, 1331712],
  [387072, -529920, 235008, 237312, 1175040, 357120, -2089728, -1880064, -1741824, -377856, 6091776, -142848, -1022976, 1787904, -324864, 566784, 1013760, -94464, 262656, 539136, -472320, 3220992, 105984],
  [124416, 253440, -635904, 101376, 18432, -359424, -838656, -787968, -497664, 1294848, -142848, 4515840, -400896, -368640, -1257984, -41472, -170496, 520704, -41472, -373248, 32256, 304128, -1622016],
  [622080, -179712, -1022976, 191232, -548352, 223488, -421632, 2004480, 1658880, 663552, -1022976, -400896, 981504, 248832, 89856, -373248, 13824, -117504, -857088, -539136, -255744, 594432, 967680],
  [414720, -599040, 2128896, 101376, 248832, 552960, -4156416, 967680, 248832, 755712, 1787904, -368640, 248832, 3806208, -331776, -783360, 1013760, -755712, -1410048, -304128, -1078272, 903168, 3022848],
  [-131328, 145152, -380160, -72576, 200448, -86400, 3037824, -1002240, 960768, 214272, -324864, -1257984, 89856, -331776, 3231360, 1230336, -322560, 466560, 1244160, -172800, 1731456, -926208, -13824],
  [-1064448, 235008, 2474496, -225792, 516096, -391680, 1704960, -3483648, -1548288, -1304064, 566784, -41472, -373248, -783360, 1230336, 4128768, -59904, 414720, 3013632, 1216512, 1999872, -142848, -1082880],
  [327168, -434688, -69120, 104448, 304128, 190464, -1603584, 258048, -138240, -82944, 1013760, -170496, 13824, 1013760, -322560, -59904, 692736, -179712, -723456, -9216, -967680, 1096704, 1377792],
  [145152, 149760, -1085184, 10368, -62208, -137088, 1342080, -1057536, 725760, 182016, -94464, 520704, -117504, -755712, 466560, 414720, -179712, 904320, 566784, -269568, -116352, 13824, -930816],
  [-1741824, 728064, 2820096, -516096, 96768, -580608, 3096576, -2985984, -1658880, -304128, 262656, -41472, -857088, -1410048, 1244160, 3013632, -723456, 566784, 5308416, 801792, 2985984, -2211840, -1534464],
  [-525312, 193536, 2488320, -195840, 373248, -145152, 490752, -1824768, -1313280, -1009152, 539136, -373248, -539136, -304128, -172800, 1216512, -9216, -269568, 801792, 1161216, 601344, 124416, -815616],
  [-1375488, 693504, 1969920, -268416, 246528, -466560, 3583872, -1320192, -1375488, -103680, -472320, 32256, -255744, -1078272, 1731456, 1999872, -967680, -116352, 2985984, 601344, 3636864, -1732608, -2156544],
  [1575936, -774144, -1465344, 668160, -156672, 442368, -2608128, 428544, -193536, 64512, 3220992, 304128, 594432, 903168, -926208, -142848, 1096704, 13824, -2211840, 124416, -1732608, 5469696, 92160],
  [442368, -990720, -110592, 59904, 36864, 612864, -4428288, 2543616, 677376, 1331712, 105984, -1622016, 967680, 3022848, -13824, -1082880, 1377792, -930816, -1534464, -815616, -2156544, 92160, 5686272]]

theorem amb_356k0 : x2KeyMult 0 blk_356k0 0 * x2KeyMult 0 blk_356k0 1 * x2KeyMult 0 blk_356k0 2 = 550 := by
  decide +kernel

theorem chk_356k0 : ∀ c < x2KeySize 0 blk_356k0, ∀ c' < x2KeySize 0 blk_356k0,
    x2TgtNum 72 6 blk_356k0 (x2JAll.getD (x2KeyGlobal 0 blk_356k0) []) c c' = (t8_356k0.getD c []).getD c' 0 := by
  decide +kernel

theorem tgt_356k0 : x2Target x2DataConcrete blk_356k0 =
    Matrix.of fun (c c' : x2Col 0 blk_356k0) => (((t8_356k0.getD c []).getD c' 0 : ℤ) : ℚ) / 8 :=
  x2Target_eq_lit x2DataConcrete blk_356k0 72 6 _ (fun c c' => (t8_356k0.getD c []).getD c' 0)
    (x2Target_eq_of_check x2DataConcrete blk_356k0 72 6 _ (by norm_num) (x2JAll_length_h blk_356k0)
      (x2ImageCols_concrete blk_356k0) (by rw [amb_356k0]; norm_num) (by rw [amb_356k0]; norm_num)) chk_356k0

end ThreeCopyQutritWerner.X2.Tgt
