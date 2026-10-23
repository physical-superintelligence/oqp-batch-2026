module

public import ThreeCopyQutritWerner.CertificateX2OutputConcrete
public import ThreeCopyQutritWerner.CertificateX2OutputSplit

@[expose] public section


/-! Output stage: targets `x2Target x2DataConcrete b = T8 / 8` of h blocks
555-0. The kernel computes `Jᵀ (M ⊗ M ⊗ M) J` from the images of CertificateX2Images and the local tables
of CertificateX2Reduced (W = 72). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThreeCopyQutritWerner.X2.Tgt

/-- h block `555-0`. -/
def blk_555k0 : x2Key 0 := ⟨112, by decide⟩

/-- `T8 = Jᵀ (M ⊗ M ⊗ M) J` of block `555-0`. -/
def t8_555k0 : List (List ℤ) := [
  [45100800, -73301760, 518400, -26956800, 7741440, 9745920, -90097920, -13271040, -94970880, -63555840],
  [-73301760, 68967936, 649728, 6697728, -6317568, -24572160, 37967616, -6220800, 69797376, 44478720],
  [518400, 649728, 215424, -746496, 182016, 86400, -1976832, 362880, -940032, -2557440],
  [-26956800, 6697728, -746496, 5577984, -1119744, -8294400, 12400128, -1762560, 19657728, 17210880],
  [7741440, -6317568, 182016, -1119744, 739584, 1382400, -2308608, 1831680, -8460288, -4838400],
  [9745920, -24572160, 86400, -8294400, 1382400, 6376320, -17521920, -10730880, -33177600, -6739200],
  [-90097920, 37967616, -1976832, 12400128, -2308608, -17521920, 102871296, -9227520, 84312576, 56505600],
  [-13271040, -6220800, 362880, -1762560, 1831680, -10730880, -9227520, -7516800, -3317760, -5702400],
  [-94970880, 69797376, -940032, 19657728, -8460288, -33177600, 84312576, -3317760, 91155456, 89164800],
  [-63555840, 44478720, -2557440, 17210880, -4838400, -6739200, 56505600, -5702400, 89164800, 45308160]]

theorem amb_555k0 : x2KeyMult 0 blk_555k0 0 * x2KeyMult 0 blk_555k0 1 * x2KeyMult 0 blk_555k0 2 = 1000 := by
  decide +kernel

theorem chk_555k0 : ∀ c < x2KeySize 0 blk_555k0, ∀ c' < x2KeySize 0 blk_555k0,
    x2TgtNum 72 7 blk_555k0 (x2JAll.getD (x2KeyGlobal 0 blk_555k0) []) c c' = (t8_555k0.getD c []).getD c' 0 := by
  decide +kernel

theorem tgt_555k0 : x2Target x2DataConcrete blk_555k0 =
    Matrix.of fun (c c' : x2Col 0 blk_555k0) => (((t8_555k0.getD c []).getD c' 0 : ℤ) : ℚ) / 8 :=
  x2Target_eq_lit x2DataConcrete blk_555k0 72 7 _ (fun c c' => (t8_555k0.getD c []).getD c' 0)
    (x2Target_eq_of_check x2DataConcrete blk_555k0 72 7 _ (by norm_num) (x2JAll_length_h blk_555k0)
      (x2ImageCols_concrete blk_555k0) (by rw [amb_555k0]; norm_num) (by rw [amb_555k0]; norm_num)) chk_555k0

end ThreeCopyQutritWerner.X2.Tgt
