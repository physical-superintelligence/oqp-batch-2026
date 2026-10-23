module

public import ThreeCopyQutritWerner.CertificateX2OutputConcrete
public import ThreeCopyQutritWerner.CertificateX2OutputSplit

@[expose] public section


/-! Output stage: targets `x2Target x2DataConcrete b = T8 / 8` of h blocks
555-1. The kernel computes `Jᵀ (M ⊗ M ⊗ M) J` from the images of CertificateX2Images and the local tables
of CertificateX2Reduced (W = 72). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThreeCopyQutritWerner.X2.Tgt

/-- h block `555-1`. -/
def blk_555k1 : x2Key 0 := ⟨113, by decide⟩

/-- `T8 = Jᵀ (M ⊗ M ⊗ M) J` of block `555-1`. -/
def t8_555k1 : List (List ℤ) := [
  [322560, -783360, -253440, -506880],
  [-783360, 1451520, 299520, 622080],
  [-253440, 299520, 1324800, 126720],
  [-506880, 622080, 126720, 311040]]

theorem amb_555k1 : x2KeyMult 0 blk_555k1 0 * x2KeyMult 0 blk_555k1 1 * x2KeyMult 0 blk_555k1 2 = 1000 := by
  decide +kernel

theorem chk_555k1 : ∀ c < x2KeySize 0 blk_555k1, ∀ c' < x2KeySize 0 blk_555k1,
    x2TgtNum 72 7 blk_555k1 (x2JAll.getD (x2KeyGlobal 0 blk_555k1) []) c c' = (t8_555k1.getD c []).getD c' 0 := by
  decide +kernel

theorem tgt_555k1 : x2Target x2DataConcrete blk_555k1 =
    Matrix.of fun (c c' : x2Col 0 blk_555k1) => (((t8_555k1.getD c []).getD c' 0 : ℤ) : ℚ) / 8 :=
  x2Target_eq_lit x2DataConcrete blk_555k1 72 7 _ (fun c c' => (t8_555k1.getD c []).getD c' 0)
    (x2Target_eq_of_check x2DataConcrete blk_555k1 72 7 _ (by norm_num) (x2JAll_length_h blk_555k1)
      (x2ImageCols_concrete blk_555k1) (by rw [amb_555k1]; norm_num) (by rw [amb_555k1]; norm_num)) chk_555k1

end ThreeCopyQutritWerner.X2.Tgt
