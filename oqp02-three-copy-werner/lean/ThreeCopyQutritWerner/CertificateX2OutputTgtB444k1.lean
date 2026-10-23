module

public import ThreeCopyQutritWerner.CertificateX2OutFastTgtMeta
public import ThreeCopyQutritWerner.CertificateX2OutputConcrete

@[expose] public section


/-! Output stage: target `x2Target x2DataConcrete b = T8 / 8` of h block 444-1.
The kernel computes `Jᵀ (M ⊗ M ⊗ M) J` by chunks of rows `x₂ = a` (CertificateX2OutFastTgt) from the images of
CertificateX2Images and the local tables of CertificateX2Reduced (W = 72); chunk literals at build time. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 4096

namespace ThreeCopyQutritWerner.X2.Tgt

/-- h block `444-1`. -/
def blk_444k1 : x2Key 0 := ⟨101, by decide⟩

/-- `T8 = Jᵀ (M ⊗ M ⊗ M) J` of block `444-1`. -/
def t8_444k1 : List (List ℤ) := [
  [707040, -207648, 2354688, 9792, -583488, 3276576, -412128, -606816, 1350144, -542304, -1156608, -1374336, 203904, 35424, 255744, -364032, 9504, -3514752],
  [-207648, 820704, -43200, 278016, -650880, -1200096, -70560, 1384992, -62784, 438048, -203904, 279936, 81216, 2016, 425088, 7488, -264672, 225216],
  [2354688, -43200, 2396160, 495936, -452160, 1767168, 419904, -130752, 556992, 237888, -767808, -698688, 1712448, 298944, 587520, 774720, -665280, -1045440],
  [9792, 278016, 495936, 613632, -565632, -357696, 142272, 746496, -18432, 20736, -60480, -209088, -535680, 103680, -72576, 184320, -374400, 11520],
  [-583488, -650880, -452160, -565632, 5707008, -638784, 98496, 1113984, -1236096, -1279872, 1296576, 463680, 1382400, -273024, -1302912, 688896, 753408, 680832],
  [3276576, -1200096, 1767168, -357696, -638784, 3760416, -216864, -3027744, 240768, -191520, -624384, 73728, 991872, 320544, 1209600, -130752, -85536, -1731456],
  [-412128, -70560, 419904, 142272, 98496, -216864, 505440, -170208, 44928, -163296, 378432, -84672, -404352, 25056, -715392, 528768, -80352, 207360],
  [-606816, 1384992, -130752, 746496, 1113984, -3027744, -170208, 4380768, 472896, -183456, 275328, 368640, -426816, -180576, -48384, -339264, -192672, -537408],
  [1350144, -62784, 556992, -18432, -1236096, 240768, 44928, 472896, 1183104, 55872, -224064, -165312, 366336, -60480, 24192, -175104, 77760, -777600],
  [-542304, 438048, 237888, 20736, -1279872, -191520, -163296, -183456, 55872, 606816, -427392, 315648, 146880, 33696, 504576, 149184, -199584, 271296],
  [-1156608, -203904, -767808, -60480, 1296576, -624384, 378432, 275328, -224064, -427392, 775296, 222336, -558144, -134784, -946944, -78912, 290304, 540864],
  [-1374336, 279936, -698688, -209088, 463680, 73728, -84672, 368640, -165312, 315648, 222336, 619776, 53568, -27648, -3456, -345024, 120960, 139968],
  [203904, 81216, 1712448, -535680, 1382400, 991872, -404352, -426816, 366336, 146880, -558144, 53568, 2146176, -63936, 570240, 801792, 164160, -1161216],
  [35424, 2016, 298944, 103680, -273024, 320544, 25056, -180576, -60480, 33696, -134784, -27648, -63936, 58464, 41472, 88128, -109152, -98496],
  [255744, 425088, 587520, -72576, -1302912, 1209600, -715392, -48384, 24192, 504576, -946944, -3456, 570240, 41472, 1192320, -276480, -165888, -787968],
  [-364032, 7488, 774720, 184320, 688896, -130752, 528768, -339264, -175104, 149184, -78912, -345024, 801792, 88128, -276480, 887616, -260928, 732672],
  [9504, -264672, -665280, -374400, 753408, -85536, -80352, -192672, 77760, -199584, 290304, 120960, 164160, -109152, -165888, -260928, 341856, 46656],
  [-3514752, 225216, -1045440, 11520, 680832, -1731456, 207360, -537408, -777600, 271296, 540864, 139968, -1161216, -98496, -787968, 732672, 46656, 1893888]]

x2_out_jd jdT_444k1 x2J_101 18 3375
x2_out_tgt_lits CT_444k1 72 4 4 4 18 jdT_444k1 x2J_101

theorem shapeT_444k1 : x2KeyMult 0 blk_444k1 0 = 15 ∧ x2KeyMult 0 blk_444k1 1 = 15 ∧
    x2KeyMult 0 blk_444k1 2 = 15 ∧ x2KeySize 0 blk_444k1 = 18 := by
  decide +kernel

theorem hJcT_444k1 : x2J_101.length = x2KeySize 0 blk_444k1 := by
  decide +kernel

theorem jdT_444k1_eq : jdT_444k1 = (List.range (x2KeySize 0 blk_444k1)).map fun c =>
    digs 11 (x2KeyMult 0 blk_444k1 0 * x2KeyMult 0 blk_444k1 1 * x2KeyMult 0 blk_444k1 2) (x2J_101.getD c 0) := by
  decide +kernel

theorem ct_444k1_0 : x2FTOK 72 blk_444k1 jdT_444k1 x2J_101 0 (CT_444k1_LT.getD 0 []) = true := by
  decide +kernel

theorem ct_444k1_1 : x2FTOK 72 blk_444k1 jdT_444k1 x2J_101 1 (CT_444k1_LT.getD 1 []) = true := by
  decide +kernel

theorem ct_444k1_2 : x2FTOK 72 blk_444k1 jdT_444k1 x2J_101 2 (CT_444k1_LT.getD 2 []) = true := by
  decide +kernel

theorem ct_444k1_3 : x2FTOK 72 blk_444k1 jdT_444k1 x2J_101 3 (CT_444k1_LT.getD 3 []) = true := by
  decide +kernel

theorem ct_444k1_4 : x2FTOK 72 blk_444k1 jdT_444k1 x2J_101 4 (CT_444k1_LT.getD 4 []) = true := by
  decide +kernel

theorem ct_444k1_5 : x2FTOK 72 blk_444k1 jdT_444k1 x2J_101 5 (CT_444k1_LT.getD 5 []) = true := by
  decide +kernel

theorem ct_444k1_6 : x2FTOK 72 blk_444k1 jdT_444k1 x2J_101 6 (CT_444k1_LT.getD 6 []) = true := by
  decide +kernel

theorem ct_444k1_7 : x2FTOK 72 blk_444k1 jdT_444k1 x2J_101 7 (CT_444k1_LT.getD 7 []) = true := by
  decide +kernel

theorem ct_444k1_8 : x2FTOK 72 blk_444k1 jdT_444k1 x2J_101 8 (CT_444k1_LT.getD 8 []) = true := by
  decide +kernel

theorem ct_444k1_9 : x2FTOK 72 blk_444k1 jdT_444k1 x2J_101 9 (CT_444k1_LT.getD 9 []) = true := by
  decide +kernel

theorem ct_444k1_10 : x2FTOK 72 blk_444k1 jdT_444k1 x2J_101 10 (CT_444k1_LT.getD 10 []) = true := by
  decide +kernel

theorem ct_444k1_11 : x2FTOK 72 blk_444k1 jdT_444k1 x2J_101 11 (CT_444k1_LT.getD 11 []) = true := by
  decide +kernel

theorem ct_444k1_12 : x2FTOK 72 blk_444k1 jdT_444k1 x2J_101 12 (CT_444k1_LT.getD 12 []) = true := by
  decide +kernel

theorem ct_444k1_13 : x2FTOK 72 blk_444k1 jdT_444k1 x2J_101 13 (CT_444k1_LT.getD 13 []) = true := by
  decide +kernel

theorem ct_444k1_14 : x2FTOK 72 blk_444k1 jdT_444k1 x2J_101 14 (CT_444k1_LT.getD 14 []) = true := by
  decide +kernel

theorem hsumT_444k1 : (Matrix.of fun (c c' : x2Col 0 blk_444k1) =>
    rsum (fun a => ent 72 (72 - 1) ((CT_444k1_LT.getD a []).getD c' 0) c) (x2KeyMult 0 blk_444k1 2)) =
    Matrix.of fun (c c' : x2Col 0 blk_444k1) => (t8_444k1.getD c []).getD c' 0 := by
  decide +kernel

theorem tgt_444k1 : x2Target x2DataConcrete blk_444k1 =
    Matrix.of fun (c c' : x2Col 0 blk_444k1) => (((t8_444k1.getD c []).getD c' 0 : ℤ) : ℚ) / 8 := by
  obtain ⟨h0, h1, h2, hr⟩ := shapeT_444k1
  refine x2Target_of_chunks x2DataConcrete blk_444k1 72 jdT_444k1 x2J_101 CT_444k1_LT
    (Matrix.of fun (c c' : x2Col 0 blk_444k1) => (t8_444k1.getD c []).getD c' 0) (x2ImageCols_concrete blk_444k1)
    (by norm_num) hJcT_444k1 (xf_jd_ok _ _ _ _ jdT_444k1_eq) ?_ ?_ ?_ hsumT_444k1
  · rw [h0, h1, h2]; norm_num
  · rw [h0, h1, h2]; norm_num
  · intro a ha
    rw [h2] at ha
    interval_cases a
    · exact ct_444k1_0
    · exact ct_444k1_1
    · exact ct_444k1_2
    · exact ct_444k1_3
    · exact ct_444k1_4
    · exact ct_444k1_5
    · exact ct_444k1_6
    · exact ct_444k1_7
    · exact ct_444k1_8
    · exact ct_444k1_9
    · exact ct_444k1_10
    · exact ct_444k1_11
    · exact ct_444k1_12
    · exact ct_444k1_13
    · exact ct_444k1_14

end ThreeCopyQutritWerner.X2.Tgt
