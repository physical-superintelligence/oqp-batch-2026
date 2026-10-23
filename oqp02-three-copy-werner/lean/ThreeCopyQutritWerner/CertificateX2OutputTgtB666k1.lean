module

public import ThreeCopyQutritWerner.CertificateX2OutputConcrete
public import ThreeCopyQutritWerner.CertificateX2OutputSplit

@[expose] public section


/-! Output stage: targets `x2Target x2DataConcrete b = T8 / 8` of h blocks
666-1. The kernel computes `Jᵀ (M ⊗ M ⊗ M) J` from the images of CertificateX2Images and the local tables
of CertificateX2Reduced (W = 72). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThreeCopyQutritWerner.X2.Tgt

/-- h block `666-1`. -/
def blk_666k1 : x2Key 0 := ⟨120, by decide⟩

/-- `T8 = Jᵀ (M ⊗ M ⊗ M) J` of block `666-1`. -/
def t8_666k1 : List (List ℤ) := [
  [-5062656, 7372800, 4202496, -983040, -2506752, -8331264, -3907584],
  [7372800, 53821440, -32440320, 13271040, 47923200, 47923200, 23592960],
  [4202496, -32440320, 73175040, -23150592, -4055040, 5124096, -28495872],
  [-983040, 13271040, -23150592, 98304, 24182784, 4571136, 5455872],
  [-2506752, 47923200, -4055040, 24182784, 33914880, -39739392, 3170304],
  [-8331264, 47923200, 5124096, 4571136, -39739392, 20533248, -258048],
  [-3907584, 23592960, -28495872, 5455872, 3170304, -258048, 6819840]]

theorem amb_666k1 : x2KeyMult 0 blk_666k1 0 * x2KeyMult 0 blk_666k1 1 * x2KeyMult 0 blk_666k1 2 = 1331 := by
  decide +kernel

theorem chk_666k1 : ∀ c < x2KeySize 0 blk_666k1, ∀ c' < x2KeySize 0 blk_666k1,
    x2TgtNum 72 7 blk_666k1 (x2JAll.getD (x2KeyGlobal 0 blk_666k1) []) c c' = (t8_666k1.getD c []).getD c' 0 := by
  decide +kernel

theorem tgt_666k1 : x2Target x2DataConcrete blk_666k1 =
    Matrix.of fun (c c' : x2Col 0 blk_666k1) => (((t8_666k1.getD c []).getD c' 0 : ℤ) : ℚ) / 8 :=
  x2Target_eq_lit x2DataConcrete blk_666k1 72 7 _ (fun c c' => (t8_666k1.getD c []).getD c' 0)
    (x2Target_eq_of_check x2DataConcrete blk_666k1 72 7 _ (by norm_num) (x2JAll_length_h blk_666k1)
      (x2ImageCols_concrete blk_666k1) (by rw [amb_666k1]; norm_num) (by rw [amb_666k1]; norm_num)) chk_666k1

end ThreeCopyQutritWerner.X2.Tgt
