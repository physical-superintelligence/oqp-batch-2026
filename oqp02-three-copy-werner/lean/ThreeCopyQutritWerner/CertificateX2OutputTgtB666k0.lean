module

public import ThreeCopyQutritWerner.CertificateX2OutputConcrete
public import ThreeCopyQutritWerner.CertificateX2OutputSplit

@[expose] public section


/-! Output stage: targets `x2Target x2DataConcrete b = T8 / 8` of h blocks
666-0. The kernel computes `Jᵀ (M ⊗ M ⊗ M) J` from the images of CertificateX2Images and the local tables
of CertificateX2Reduced (W = 72). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThreeCopyQutritWerner.X2.Tgt

/-- h block `666-0`. -/
def blk_666k0 : x2Key 0 := ⟨119, by decide⟩

/-- `T8 = Jᵀ (M ⊗ M ⊗ M) J` of block `666-0`. -/
def t8_666k0 : List (List ℤ) := [
  [5013504, 11943936, -11059200, 11943936, 884736, -12828672, -9142272, 4423680, -11943936, 4276224],
  [11943936, 116822016, -15888384, 78667776, 4276224, -38486016, -7520256, 32034816, -27684864, 6414336],
  [-11059200, -15888384, 37638144, -23961600, -2359296, 25657344, 18726912, -7778304, 24956928, -10248192],
  [11943936, 78667776, -23961600, 117153792, 3686400, -2433024, 3391488, 36569088, 2285568, 4497408],
  [884736, 4276224, -2359296, 3686400, 245760, -3833856, 393216, 3244032, -1769472, 688128],
  [-12828672, -38486016, 25657344, -2433024, -3833856, 36052992, 29638656, 1105920, 46006272, -12607488],
  [-9142272, -7520256, 18726912, 3391488, 393216, 29638656, 17301504, -2359296, 26689536, -8699904],
  [4423680, 32034816, -7778304, 36569088, 3244032, 1105920, -2359296, 8220672, 2248704, 2064384],
  [-11943936, -27684864, 24956928, 2285568, -1769472, 46006272, 26689536, 2248704, 32329728, -11722752],
  [4276224, 6414336, -10248192, 4497408, 688128, -12607488, -8699904, 2064384, -11722752, 4251648]]

theorem amb_666k0 : x2KeyMult 0 blk_666k0 0 * x2KeyMult 0 blk_666k0 1 * x2KeyMult 0 blk_666k0 2 = 1331 := by
  decide +kernel

theorem chk_666k0 : ∀ c < x2KeySize 0 blk_666k0, ∀ c' < x2KeySize 0 blk_666k0,
    x2TgtNum 72 7 blk_666k0 (x2JAll.getD (x2KeyGlobal 0 blk_666k0) []) c c' = (t8_666k0.getD c []).getD c' 0 := by
  decide +kernel

theorem tgt_666k0 : x2Target x2DataConcrete blk_666k0 =
    Matrix.of fun (c c' : x2Col 0 blk_666k0) => (((t8_666k0.getD c []).getD c' 0 : ℤ) : ℚ) / 8 :=
  x2Target_eq_lit x2DataConcrete blk_666k0 72 7 _ (fun c c' => (t8_666k0.getD c []).getD c' 0)
    (x2Target_eq_of_check x2DataConcrete blk_666k0 72 7 _ (by norm_num) (x2JAll_length_h blk_666k0)
      (x2ImageCols_concrete blk_666k0) (by rw [amb_666k0]; norm_num) (by rw [amb_666k0]; norm_num)) chk_666k0

end ThreeCopyQutritWerner.X2.Tgt
