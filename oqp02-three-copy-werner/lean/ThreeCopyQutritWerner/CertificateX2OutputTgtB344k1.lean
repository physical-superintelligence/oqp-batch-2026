module

public import ThreeCopyQutritWerner.CertificateX2OutFastTgtMeta
public import ThreeCopyQutritWerner.CertificateX2OutputConcrete

@[expose] public section


/-! Output stage: target `x2Target x2DataConcrete b = T8 / 8` of h block 344-1.
The kernel computes `Jᵀ (M ⊗ M ⊗ M) J` by chunks of rows `x₂ = a` (CertificateX2OutFastTgt) from the images of
CertificateX2Images and the local tables of CertificateX2Reduced (W = 72); chunk literals at build time. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 4096

namespace ThreeCopyQutritWerner.X2.Tgt

/-- h block `344-1`. -/
def blk_344k1 : x2Key 0 := ⟨92, by decide⟩

/-- `T8 = Jᵀ (M ⊗ M ⊗ M) J` of block `344-1`. -/
def t8_344k1 : List (List ℤ) := [
  [3291840, 241344, -202176, 212544, -101952, -143424, 667008, 585792, -651456, 127872, -17280, -1866240, 518400, 302400, 145152, -273024, 3456, 492480, 373248, -57024, -39744],
  [241344, 192704, 72000, 3648, 88128, -71616, 128640, 146880, -6336, -196224, 49920, -95616, 15360, -6848, -44544, -81024, -13568, -2880, 271872, -184128, -158400],
  [-202176, 72000, 1620864, -382464, -623808, 659520, 220032, -439488, 407808, -47808, -411840, 84096, -180864, 78336, -165312, -901440, 139392, -362304, 785664, -211392, -228096],
  [212544, 3648, -382464, 1058688, 179136, 40896, 21888, -661824, -4608, 331200, 120384, -279936, -31104, 10752, 29376, 134208, -74496, 134208, -283392, 241344, 223488],
  [-101952, 88128, -623808, 179136, 1280448, -283968, 43776, 351936, -36288, -464256, 177408, -114624, -291456, 62208, 173376, 524160, -42624, 116352, -50688, -263232, -309312],
  [-143424, -71616, 659520, 40896, -283968, 1392192, 131328, -279360, 366912, 288000, -240768, 52416, -256896, 135552, -300096, 241920, 76800, -391680, 105984, 245952, 235584],
  [667008, 128640, 220032, 21888, 43776, 131328, 460800, 41472, -283968, -78336, -13824, -134784, 315648, 60288, 189504, -16128, 9600, 337536, 297216, -150912, -102528],
  [585792, 146880, -439488, -661824, 351936, -279360, 41472, 1520640, -239616, -521856, 48960, -416448, -81792, -11520, 40896, -6912, -8064, 99648, 238464, -229824, -180864],
  [-651456, -6336, 407808, -4608, -36288, 366912, -283968, -239616, 677376, 120384, -142848, 299520, -429120, -44928, -474048, -52416, 66816, -525888, 240768, -23616, -32832],
  [127872, -196224, -47808, 331200, -464256, 288000, -78336, -521856, 120384, 648000, -152640, 17280, 137088, 21696, 21312, 186048, 41856, -97920, -317952, 414720, 300096],
  [-17280, 49920, -411840, 120384, 177408, -240768, -13824, 48960, -142848, -152640, 215424, 90432, 47232, -75264, 92160, 181440, -64896, 92160, -201600, 19584, 26496],
  [-1866240, -95616, 84096, -279936, -114624, 52416, -134784, -416448, 299520, 17280, 90432, 1886976, 70272, -204480, -55872, 584064, -24768, -135360, -221184, -70848, 52416],
  [518400, 15360, -180864, -31104, -291456, -256896, 315648, -81792, -429120, 137088, 47232, 70272, 751104, -127104, 317376, -102528, -4992, 516096, -126720, 94464, 14976],
  [302400, -6848, 78336, 10752, 62208, 135552, 60288, -11520, -44928, 21696, -75264, -204480, -127104, 101888, -14784, 48192, 23360, -17856, 87552, -4224, -42048],
  [145152, -44544, -165312, 29376, 173376, -300096, 189504, 40896, -474048, 21312, 92160, -55872, 317376, -14784, 633600, -97344, -30912, 438336, -188928, -576, -2304],
  [-273024, -81024, -901440, 134208, 524160, 241920, -16128, -6912, -52416, 186048, 181440, 584064, -102528, 48192, -97344, 1433664, -52608, -18432, -546048, 205056, 251712],
  [3456, -13568, 139392, -74496, -42624, 76800, 9600, -8064, 66816, 41856, -64896, -24768, -4992, 23360, -30912, -52608, 25472, -67392, 66816, -9984, -14976],
  [492480, -2880, -362304, 134208, 116352, -391680, 337536, 99648, -525888, -97920, 92160, -135360, 516096, -17856, 438336, -18432, -67392, 630144, -171648, -33408, -10944],
  [373248, 271872, 785664, -283392, -50688, 105984, 297216, 238464, 240768, -317952, -201600, -221184, -126720, 87552, -188928, -546048, 66816, -171648, 753408, -380160, -326016],
  [-57024, -184128, -211392, 241344, -263232, 245952, -150912, -229824, -23616, 414720, 19584, -70848, 94464, -4224, -576, 205056, -9984, -33408, -380160, 340416, 342720],
  [-39744, -158400, -228096, 223488, -309312, 235584, -102528, -180864, -32832, 300096, 26496, 52416, 14976, -42048, -2304, 251712, -14976, -10944, -326016, 342720, 309312]]

x2_out_jd jdT_344k1 x2J_92 21 1125
x2_out_tgt_lits CT_344k1 72 3 4 4 21 jdT_344k1 x2J_92

theorem shapeT_344k1 : x2KeyMult 0 blk_344k1 0 = 5 ∧ x2KeyMult 0 blk_344k1 1 = 15 ∧
    x2KeyMult 0 blk_344k1 2 = 15 ∧ x2KeySize 0 blk_344k1 = 21 := by
  decide +kernel

theorem hJcT_344k1 : x2J_92.length = x2KeySize 0 blk_344k1 := by
  decide +kernel

theorem jdT_344k1_eq : jdT_344k1 = (List.range (x2KeySize 0 blk_344k1)).map fun c =>
    digs 11 (x2KeyMult 0 blk_344k1 0 * x2KeyMult 0 blk_344k1 1 * x2KeyMult 0 blk_344k1 2) (x2J_92.getD c 0) := by
  decide +kernel

theorem ct_344k1_0 : x2FTOK 72 blk_344k1 jdT_344k1 x2J_92 0 (CT_344k1_LT.getD 0 []) = true := by
  decide +kernel

theorem ct_344k1_1 : x2FTOK 72 blk_344k1 jdT_344k1 x2J_92 1 (CT_344k1_LT.getD 1 []) = true := by
  decide +kernel

theorem ct_344k1_2 : x2FTOK 72 blk_344k1 jdT_344k1 x2J_92 2 (CT_344k1_LT.getD 2 []) = true := by
  decide +kernel

theorem ct_344k1_3 : x2FTOK 72 blk_344k1 jdT_344k1 x2J_92 3 (CT_344k1_LT.getD 3 []) = true := by
  decide +kernel

theorem ct_344k1_4 : x2FTOK 72 blk_344k1 jdT_344k1 x2J_92 4 (CT_344k1_LT.getD 4 []) = true := by
  decide +kernel

theorem ct_344k1_5 : x2FTOK 72 blk_344k1 jdT_344k1 x2J_92 5 (CT_344k1_LT.getD 5 []) = true := by
  decide +kernel

theorem ct_344k1_6 : x2FTOK 72 blk_344k1 jdT_344k1 x2J_92 6 (CT_344k1_LT.getD 6 []) = true := by
  decide +kernel

theorem ct_344k1_7 : x2FTOK 72 blk_344k1 jdT_344k1 x2J_92 7 (CT_344k1_LT.getD 7 []) = true := by
  decide +kernel

theorem ct_344k1_8 : x2FTOK 72 blk_344k1 jdT_344k1 x2J_92 8 (CT_344k1_LT.getD 8 []) = true := by
  decide +kernel

theorem ct_344k1_9 : x2FTOK 72 blk_344k1 jdT_344k1 x2J_92 9 (CT_344k1_LT.getD 9 []) = true := by
  decide +kernel

theorem ct_344k1_10 : x2FTOK 72 blk_344k1 jdT_344k1 x2J_92 10 (CT_344k1_LT.getD 10 []) = true := by
  decide +kernel

theorem ct_344k1_11 : x2FTOK 72 blk_344k1 jdT_344k1 x2J_92 11 (CT_344k1_LT.getD 11 []) = true := by
  decide +kernel

theorem ct_344k1_12 : x2FTOK 72 blk_344k1 jdT_344k1 x2J_92 12 (CT_344k1_LT.getD 12 []) = true := by
  decide +kernel

theorem ct_344k1_13 : x2FTOK 72 blk_344k1 jdT_344k1 x2J_92 13 (CT_344k1_LT.getD 13 []) = true := by
  decide +kernel

theorem ct_344k1_14 : x2FTOK 72 blk_344k1 jdT_344k1 x2J_92 14 (CT_344k1_LT.getD 14 []) = true := by
  decide +kernel

theorem hsumT_344k1 : (Matrix.of fun (c c' : x2Col 0 blk_344k1) =>
    rsum (fun a => ent 72 (72 - 1) ((CT_344k1_LT.getD a []).getD c' 0) c) (x2KeyMult 0 blk_344k1 2)) =
    Matrix.of fun (c c' : x2Col 0 blk_344k1) => (t8_344k1.getD c []).getD c' 0 := by
  decide +kernel

theorem tgt_344k1 : x2Target x2DataConcrete blk_344k1 =
    Matrix.of fun (c c' : x2Col 0 blk_344k1) => (((t8_344k1.getD c []).getD c' 0 : ℤ) : ℚ) / 8 := by
  obtain ⟨h0, h1, h2, hr⟩ := shapeT_344k1
  refine x2Target_of_chunks x2DataConcrete blk_344k1 72 jdT_344k1 x2J_92 CT_344k1_LT
    (Matrix.of fun (c c' : x2Col 0 blk_344k1) => (t8_344k1.getD c []).getD c' 0) (x2ImageCols_concrete blk_344k1)
    (by norm_num) hJcT_344k1 (xf_jd_ok _ _ _ _ jdT_344k1_eq) ?_ ?_ ?_ hsumT_344k1
  · rw [h0, h1, h2]; norm_num
  · rw [h0, h1, h2]; norm_num
  · intro a ha
    rw [h2] at ha
    interval_cases a
    · exact ct_344k1_0
    · exact ct_344k1_1
    · exact ct_344k1_2
    · exact ct_344k1_3
    · exact ct_344k1_4
    · exact ct_344k1_5
    · exact ct_344k1_6
    · exact ct_344k1_7
    · exact ct_344k1_8
    · exact ct_344k1_9
    · exact ct_344k1_10
    · exact ct_344k1_11
    · exact ct_344k1_12
    · exact ct_344k1_13
    · exact ct_344k1_14

end ThreeCopyQutritWerner.X2.Tgt
