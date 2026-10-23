module

public import ThreeCopyQutritWerner.CertificateX2OutFastTgtMeta
public import ThreeCopyQutritWerner.CertificateX2OutputConcrete

@[expose] public section


/-! Output stage: target `x2Target x2DataConcrete b = T8 / 8` of h block 244-1.
The kernel computes `Jᵀ (M ⊗ M ⊗ M) J` by chunks of rows `x₂ = a` (CertificateX2OutFastTgt) from the images of
CertificateX2Images and the local tables of CertificateX2Reduced (W = 72); chunk literals at build time. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 4096

namespace ThreeCopyQutritWerner.X2.Tgt

/-- h block `244-1`. -/
def blk_244k1 : x2Key 0 := ⟨75, by decide⟩

/-- `T8 = Jᵀ (M ⊗ M ⊗ M) J` of block `244-1`. -/
def t8_244k1 : List (List ℤ) := [
  [1597056, -393984, 793728, -264576, -38400, 263808, 291072, -375552, 524928, 128640, 204288, 445440, -174720, -160896, -162048, -3264, -72192, 498624, 106368, 105216],
  [-393984, 1499904, 573696, 172800, 20736, -797184, 82944, 13824, 1002240, -228096, -23040, -103680, 1050624, 822528, 214272, 162432, 225792, 508032, 836352, -670464],
  [793728, 573696, 1586304, -1152, 94464, -33408, -451584, -158976, 685440, 284544, -131328, -29952, 88704, 420480, -170496, 129600, 99072, 142272, 406656, -4608],
  [-264576, 172800, -1152, 352896, 74496, -100224, -110976, 274176, -242304, -137472, 100608, -11904, 31488, 147840, -60672, -8064, -43392, -317568, 11904, -312960],
  [-38400, 20736, 94464, 74496, 77568, 62208, -1920, 59904, -16896, -13440, 30720, -768, 52608, 203520, -52224, -9216, -13056, -28032, -6144, -62592],
  [263808, -797184, -33408, -100224, 62208, 1038720, 261504, -57600, -369792, 596736, 21504, -46080, -435456, -480384, -57600, -52416, -84480, 62784, -445824, 339840],
  [291072, 82944, -451584, -110976, -1920, 261504, 818304, -131328, 175488, -48000, -25728, 107520, 273792, 84864, 45696, 34752, -59136, 547392, -129408, -281472],
  [-375552, 13824, -158976, 274176, 59904, -57600, -131328, 737280, 2304, -216576, 110592, -200448, 64512, -103680, -36864, -42240, 29952, -205056, -320256, -476928],
  [524928, 1002240, 685440, -242304, -16896, -369792, 175488, 2304, 1587840, 176640, 35328, 152448, 486912, 423552, -66048, 215040, 183936, 920064, 485760, -590208],
  [128640, -228096, 284544, -137472, -13440, 596736, -48000, -216576, 176640, 436992, -101760, -4224, -307968, -344832, 4224, 77760, 62592, 272064, -38400, 200064],
  [204288, -23040, -131328, 100608, 30720, 21504, -25728, 110592, 35328, -101760, 357120, 44544, 175488, 192768, -498432, -36864, -48384, 25728, -224256, -170112],
  [445440, -103680, -29952, -11904, -768, -46080, 107520, -200448, 152448, -4224, 44544, 546432, -89088, -154752, -49920, -6528, -77184, 88320, 193152, 110208],
  [-174720, 1050624, 88704, 31488, 52608, -435456, 273792, 64512, 486912, -307968, 175488, -89088, 904704, 782592, 21120, 33408, 92160, 537216, 397824, -439680],
  [-160896, 822528, 420480, 147840, 203520, -480384, 84864, -103680, 423552, -344832, 192768, -154752, 782592, 1417344, -46848, -7680, 25728, 275712, 567168, -435072],
  [-162048, 214272, -170496, -60672, -52224, -57600, 45696, -36864, -66048, 4224, -498432, -49920, 21120, -46848, 215808, 34560, 14592, -24960, 10752, 37248],
  [-3264, 162432, 129600, -8064, -9216, -52416, 34752, -42240, 215040, 77760, -36864, -6528, 33408, -7680, 34560, 35552, 42112, 136224, 98304, -76800],
  [-72192, 225792, 99072, -43392, -13056, -84480, -59136, 29952, 183936, 62592, -48384, -77184, 92160, 25728, 14592, 42112, 61312, 100608, 48000, -23424],
  [498624, 508032, 142272, -317568, -28032, 62784, 547392, -205056, 920064, 272064, 25728, 88320, 537216, 275712, -24960, 136224, 100608, 850272, 222720, -232320],
  [106368, 836352, 406656, 11904, -6144, -445824, -129408, -320256, 485760, -38400, -224256, 193152, 397824, 567168, 10752, 98304, 48000, 222720, 615552, -151680],
  [105216, -670464, -4608, -312960, -62592, 339840, -281472, -476928, -590208, 200064, -170112, 110208, -439680, -435072, 37248, -76800, -23424, -232320, -151680, 1060224]]

x2_out_jd jdT_244k1 x2J_75 20 1125
x2_out_tgt_lits CT_244k1 72 2 4 4 20 jdT_244k1 x2J_75

theorem shapeT_244k1 : x2KeyMult 0 blk_244k1 0 = 5 ∧ x2KeyMult 0 blk_244k1 1 = 15 ∧
    x2KeyMult 0 blk_244k1 2 = 15 ∧ x2KeySize 0 blk_244k1 = 20 := by
  decide +kernel

theorem hJcT_244k1 : x2J_75.length = x2KeySize 0 blk_244k1 := by
  decide +kernel

theorem jdT_244k1_eq : jdT_244k1 = (List.range (x2KeySize 0 blk_244k1)).map fun c =>
    digs 11 (x2KeyMult 0 blk_244k1 0 * x2KeyMult 0 blk_244k1 1 * x2KeyMult 0 blk_244k1 2) (x2J_75.getD c 0) := by
  decide +kernel

theorem ct_244k1_0 : x2FTOK 72 blk_244k1 jdT_244k1 x2J_75 0 (CT_244k1_LT.getD 0 []) = true := by
  decide +kernel

theorem ct_244k1_1 : x2FTOK 72 blk_244k1 jdT_244k1 x2J_75 1 (CT_244k1_LT.getD 1 []) = true := by
  decide +kernel

theorem ct_244k1_2 : x2FTOK 72 blk_244k1 jdT_244k1 x2J_75 2 (CT_244k1_LT.getD 2 []) = true := by
  decide +kernel

theorem ct_244k1_3 : x2FTOK 72 blk_244k1 jdT_244k1 x2J_75 3 (CT_244k1_LT.getD 3 []) = true := by
  decide +kernel

theorem ct_244k1_4 : x2FTOK 72 blk_244k1 jdT_244k1 x2J_75 4 (CT_244k1_LT.getD 4 []) = true := by
  decide +kernel

theorem ct_244k1_5 : x2FTOK 72 blk_244k1 jdT_244k1 x2J_75 5 (CT_244k1_LT.getD 5 []) = true := by
  decide +kernel

theorem ct_244k1_6 : x2FTOK 72 blk_244k1 jdT_244k1 x2J_75 6 (CT_244k1_LT.getD 6 []) = true := by
  decide +kernel

theorem ct_244k1_7 : x2FTOK 72 blk_244k1 jdT_244k1 x2J_75 7 (CT_244k1_LT.getD 7 []) = true := by
  decide +kernel

theorem ct_244k1_8 : x2FTOK 72 blk_244k1 jdT_244k1 x2J_75 8 (CT_244k1_LT.getD 8 []) = true := by
  decide +kernel

theorem ct_244k1_9 : x2FTOK 72 blk_244k1 jdT_244k1 x2J_75 9 (CT_244k1_LT.getD 9 []) = true := by
  decide +kernel

theorem ct_244k1_10 : x2FTOK 72 blk_244k1 jdT_244k1 x2J_75 10 (CT_244k1_LT.getD 10 []) = true := by
  decide +kernel

theorem ct_244k1_11 : x2FTOK 72 blk_244k1 jdT_244k1 x2J_75 11 (CT_244k1_LT.getD 11 []) = true := by
  decide +kernel

theorem ct_244k1_12 : x2FTOK 72 blk_244k1 jdT_244k1 x2J_75 12 (CT_244k1_LT.getD 12 []) = true := by
  decide +kernel

theorem ct_244k1_13 : x2FTOK 72 blk_244k1 jdT_244k1 x2J_75 13 (CT_244k1_LT.getD 13 []) = true := by
  decide +kernel

theorem ct_244k1_14 : x2FTOK 72 blk_244k1 jdT_244k1 x2J_75 14 (CT_244k1_LT.getD 14 []) = true := by
  decide +kernel

theorem hsumT_244k1 : (Matrix.of fun (c c' : x2Col 0 blk_244k1) =>
    rsum (fun a => ent 72 (72 - 1) ((CT_244k1_LT.getD a []).getD c' 0) c) (x2KeyMult 0 blk_244k1 2)) =
    Matrix.of fun (c c' : x2Col 0 blk_244k1) => (t8_244k1.getD c []).getD c' 0 := by
  decide +kernel

theorem tgt_244k1 : x2Target x2DataConcrete blk_244k1 =
    Matrix.of fun (c c' : x2Col 0 blk_244k1) => (((t8_244k1.getD c []).getD c' 0 : ℤ) : ℚ) / 8 := by
  obtain ⟨h0, h1, h2, hr⟩ := shapeT_244k1
  refine x2Target_of_chunks x2DataConcrete blk_244k1 72 jdT_244k1 x2J_75 CT_244k1_LT
    (Matrix.of fun (c c' : x2Col 0 blk_244k1) => (t8_244k1.getD c []).getD c' 0) (x2ImageCols_concrete blk_244k1)
    (by norm_num) hJcT_244k1 (xf_jd_ok _ _ _ _ jdT_244k1_eq) ?_ ?_ ?_ hsumT_244k1
  · rw [h0, h1, h2]; norm_num
  · rw [h0, h1, h2]; norm_num
  · intro a ha
    rw [h2] at ha
    interval_cases a
    · exact ct_244k1_0
    · exact ct_244k1_1
    · exact ct_244k1_2
    · exact ct_244k1_3
    · exact ct_244k1_4
    · exact ct_244k1_5
    · exact ct_244k1_6
    · exact ct_244k1_7
    · exact ct_244k1_8
    · exact ct_244k1_9
    · exact ct_244k1_10
    · exact ct_244k1_11
    · exact ct_244k1_12
    · exact ct_244k1_13
    · exact ct_244k1_14

end ThreeCopyQutritWerner.X2.Tgt
