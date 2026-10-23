module

public import ThreeCopyQutritWerner.CertificateX2HKeysMulCheck0_0
public import ThreeCopyQutritWerner.CertificateX2HKeysMulCheck1_0
public import ThreeCopyQutritWerner.CertificateX2HKeysMulCheck2_0
public import ThreeCopyQutritWerner.CertificateX2HKeysMulCheck3_0
public import ThreeCopyQutritWerner.CertificateX2HKeysMulCheck4_0
public import ThreeCopyQutritWerner.CertificateX2HKeysMulCheck4_1
public import ThreeCopyQutritWerner.CertificateX2HKeysMulCheck4_2
public import ThreeCopyQutritWerner.CertificateX2HKeysMulCheck4_3
public import ThreeCopyQutritWerner.CertificateX2HKeysMulCheck4_4
public import ThreeCopyQutritWerner.CertificateX2HKeysMulCheck4_5
public import ThreeCopyQutritWerner.CertificateX2HKeysMulCheck4_6
public import ThreeCopyQutritWerner.CertificateX2HKeysMulCheck4_7
public import ThreeCopyQutritWerner.CertificateX2HKeysMulCheck4_8
public import ThreeCopyQutritWerner.CertificateX2HKeysMulCheck4_9
public import ThreeCopyQutritWerner.CertificateX2HKeysMulCheck4_10
public import ThreeCopyQutritWerner.CertificateX2HKeysMulCheck4_11
public import ThreeCopyQutritWerner.CertificateX2HKeysMulCheck4_12
public import ThreeCopyQutritWerner.CertificateX2HKeysMulCheck4_13
public import ThreeCopyQutritWerner.CertificateX2HKeysMulCheck4_14
public import ThreeCopyQutritWerner.CertificateX2HKeysMulCheck4_15
public import ThreeCopyQutritWerner.CertificateX2HKeysMulCheck4_16
public import ThreeCopyQutritWerner.CertificateX2HKeysMulCheck4_17
public import ThreeCopyQutritWerner.CertificateX2HKeysMulCheck4_18
public import ThreeCopyQutritWerner.CertificateX2HKeysMulCheck4_19
public import ThreeCopyQutritWerner.CertificateX2HKeysMulCheck4_20
public import ThreeCopyQutritWerner.CertificateX2HKeysMulCheck4_21
public import ThreeCopyQutritWerner.CertificateX2HKeysMulCheck5_0
public import ThreeCopyQutritWerner.CertificateX2HKeysMulCheck5_1
public import ThreeCopyQutritWerner.CertificateX2HKeysMulCheck5_2
public import ThreeCopyQutritWerner.CertificateX2HKeysMulCheck5_3
public import ThreeCopyQutritWerner.CertificateX2HKeysMulCheck5_4
public import ThreeCopyQutritWerner.CertificateX2HKeysMulCheck5_5
public import ThreeCopyQutritWerner.CertificateX2HKeysMulCheck5_6
public import ThreeCopyQutritWerner.CertificateX2HKeysMulCheck5_7
public import ThreeCopyQutritWerner.CertificateX2HKeysMulCheck5_8
public import ThreeCopyQutritWerner.CertificateX2HKeysMulCheck5_9
public import ThreeCopyQutritWerner.CertificateX2HKeysMulCheck5_10
public import ThreeCopyQutritWerner.CertificateX2HKeysMulCheck6_0
public import ThreeCopyQutritWerner.CertificateX2HKeysMulCheck6_1
public import ThreeCopyQutritWerner.CertificateX2HKeysMulCheck6_2
public import ThreeCopyQutritWerner.CertificateX2HKeysMulCheck6_3
public import ThreeCopyQutritWerner.CertificateX2HKeysMulCheck6_4
public import ThreeCopyQutritWerner.CertificateX2HKeysMulCheck6_5
public import ThreeCopyQutritWerner.CertificateX2HKeysMulCheck6_6
public import ThreeCopyQutritWerner.CertificateX2HKeysMulCheck6_7
public import ThreeCopyQutritWerner.CertificateX2HKeysMulCheck6_8
public import ThreeCopyQutritWerner.CertificateX2HKeysMulCheck6_9
public import ThreeCopyQutritWerner.CertificateX2HKeysMulCheck6_10
public import ThreeCopyQutritWerner.CertificateX2HKeysRedCheck

@[expose] public section


/-! Per-site multiplicativity of the carrier actions on the special left factors (dispatch),
and the identity element acts by the identity (kernel). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThreeCopyQutritWerner.X2Sites

theorem x2hIdCheck0 : x2hA0 (x2hSpecial 0) = 1 := by
  decide +kernel

theorem x2hIdCheck1 : x2hA1 (x2hSpecial 0) = 1 := by
  decide +kernel

theorem x2hIdCheck2 : x2hA2 (x2hSpecial 0) = 1 := by
  decide +kernel

theorem x2hIdCheck3 : x2hA3 (x2hSpecial 0) = 1 := by
  decide +kernel

theorem x2hIdCheck4 : x2hA4 (x2hSpecial 0) = 1 := by
  decide +kernel

theorem x2hIdCheck5 : x2hA5 (x2hSpecial 0) = 1 := by
  decide +kernel

theorem x2hIdCheck6 : x2hA6 (x2hSpecial 0) = 1 := by
  decide +kernel

theorem x2hMulCheck0 (s : Fin 12) (q : Fin 120) :
    x2hA0 (x2hLMul s q) = x2hA0 (x2hSpecial s) * x2hA0 q := by
  by_cases hs0 : s = 0
  · subst hs0
    rw [x2hLMul0, x2hIdCheck0, Matrix.one_mul]
  have hs : (s : ℕ) ≠ 0 := fun h => hs0 (Fin.ext h)
  have hs' := s.isLt
  have hq := q.isLt
  · exact x2hMulCheck0_0 s q (by omega) (by omega)

theorem x2hMulCheck1 (s : Fin 12) (q : Fin 120) :
    x2hA1 (x2hLMul s q) = x2hA1 (x2hSpecial s) * x2hA1 q := by
  by_cases hs0 : s = 0
  · subst hs0
    rw [x2hLMul0, x2hIdCheck1, Matrix.one_mul]
  have hs : (s : ℕ) ≠ 0 := fun h => hs0 (Fin.ext h)
  have hs' := s.isLt
  have hq := q.isLt
  · exact x2hMulCheck1_0 s q (by omega) (by omega)

theorem x2hMulCheck2 (s : Fin 12) (q : Fin 120) :
    x2hA2 (x2hLMul s q) = x2hA2 (x2hSpecial s) * x2hA2 q := by
  by_cases hs0 : s = 0
  · subst hs0
    rw [x2hLMul0, x2hIdCheck2, Matrix.one_mul]
  have hs : (s : ℕ) ≠ 0 := fun h => hs0 (Fin.ext h)
  have hs' := s.isLt
  have hq := q.isLt
  by_cases h0 : (s : ℕ) * 120 + q < 780
  · exact x2hMulCheck2_0 s q (by omega) h0
  · exact x2hMulCheck2_1 s q (by omega) (by omega)

theorem x2hMulCheck3 (s : Fin 12) (q : Fin 120) :
    x2hA3 (x2hLMul s q) = x2hA3 (x2hSpecial s) * x2hA3 q := by
  by_cases hs0 : s = 0
  · subst hs0
    rw [x2hLMul0, x2hIdCheck3, Matrix.one_mul]
  have hs : (s : ℕ) ≠ 0 := fun h => hs0 (Fin.ext h)
  have hs' := s.isLt
  have hq := q.isLt
  by_cases h0 : (s : ℕ) * 120 + q < 780
  · exact x2hMulCheck3_0 s q (by omega) h0
  · exact x2hMulCheck3_1 s q (by omega) (by omega)

theorem x2hMulCheck4 (s : Fin 12) (q : Fin 120) :
    x2hA4 (x2hLMul s q) = x2hA4 (x2hSpecial s) * x2hA4 q := by
  by_cases hs0 : s = 0
  · subst hs0
    rw [x2hLMul0, x2hIdCheck4, Matrix.one_mul]
  have hs : (s : ℕ) ≠ 0 := fun h => hs0 (Fin.ext h)
  have hs' := s.isLt
  have hq := q.isLt
  by_cases h0 : (s : ℕ) * 120 + q < 150
  · exact x2hMulCheck4_0 s q (by omega) h0
  by_cases h1 : (s : ℕ) * 120 + q < 180
  · exact x2hMulCheck4_1 s q (by omega) h1
  by_cases h2 : (s : ℕ) * 120 + q < 210
  · exact x2hMulCheck4_2 s q (by omega) h2
  by_cases h3 : (s : ℕ) * 120 + q < 240
  · exact x2hMulCheck4_3 s q (by omega) h3
  by_cases h4 : (s : ℕ) * 120 + q < 270
  · exact x2hMulCheck4_4 s q (by omega) h4
  by_cases h5 : (s : ℕ) * 120 + q < 300
  · exact x2hMulCheck4_5 s q (by omega) h5
  by_cases h6 : (s : ℕ) * 120 + q < 330
  · exact x2hMulCheck4_6 s q (by omega) h6
  by_cases h7 : (s : ℕ) * 120 + q < 360
  · exact x2hMulCheck4_7 s q (by omega) h7
  by_cases h8 : (s : ℕ) * 120 + q < 390
  · exact x2hMulCheck4_8 s q (by omega) h8
  by_cases h9 : (s : ℕ) * 120 + q < 420
  · exact x2hMulCheck4_9 s q (by omega) h9
  by_cases h10 : (s : ℕ) * 120 + q < 450
  · exact x2hMulCheck4_10 s q (by omega) h10
  by_cases h11 : (s : ℕ) * 120 + q < 480
  · exact x2hMulCheck4_11 s q (by omega) h11
  by_cases h12 : (s : ℕ) * 120 + q < 510
  · exact x2hMulCheck4_12 s q (by omega) h12
  by_cases h13 : (s : ℕ) * 120 + q < 540
  · exact x2hMulCheck4_13 s q (by omega) h13
  by_cases h14 : (s : ℕ) * 120 + q < 570
  · exact x2hMulCheck4_14 s q (by omega) h14
  by_cases h15 : (s : ℕ) * 120 + q < 600
  · exact x2hMulCheck4_15 s q (by omega) h15
  by_cases h16 : (s : ℕ) * 120 + q < 630
  · exact x2hMulCheck4_16 s q (by omega) h16
  by_cases h17 : (s : ℕ) * 120 + q < 660
  · exact x2hMulCheck4_17 s q (by omega) h17
  by_cases h18 : (s : ℕ) * 120 + q < 690
  · exact x2hMulCheck4_18 s q (by omega) h18
  by_cases h19 : (s : ℕ) * 120 + q < 720
  · exact x2hMulCheck4_19 s q (by omega) h19
  by_cases h20 : (s : ℕ) * 120 + q < 750
  · exact x2hMulCheck4_20 s q (by omega) h20
  by_cases h21 : (s : ℕ) * 120 + q < 780
  · exact x2hMulCheck4_21 s q (by omega) h21
  by_cases h22 : (s : ℕ) * 120 + q < 810
  · exact x2hMulCheck4_22 s q (by omega) h22
  by_cases h23 : (s : ℕ) * 120 + q < 840
  · exact x2hMulCheck4_23 s q (by omega) h23
  by_cases h24 : (s : ℕ) * 120 + q < 870
  · exact x2hMulCheck4_24 s q (by omega) h24
  by_cases h25 : (s : ℕ) * 120 + q < 900
  · exact x2hMulCheck4_25 s q (by omega) h25
  by_cases h26 : (s : ℕ) * 120 + q < 930
  · exact x2hMulCheck4_26 s q (by omega) h26
  by_cases h27 : (s : ℕ) * 120 + q < 960
  · exact x2hMulCheck4_27 s q (by omega) h27
  by_cases h28 : (s : ℕ) * 120 + q < 990
  · exact x2hMulCheck4_28 s q (by omega) h28
  by_cases h29 : (s : ℕ) * 120 + q < 1020
  · exact x2hMulCheck4_29 s q (by omega) h29
  by_cases h30 : (s : ℕ) * 120 + q < 1050
  · exact x2hMulCheck4_30 s q (by omega) h30
  by_cases h31 : (s : ℕ) * 120 + q < 1080
  · exact x2hMulCheck4_31 s q (by omega) h31
  by_cases h32 : (s : ℕ) * 120 + q < 1110
  · exact x2hMulCheck4_32 s q (by omega) h32
  by_cases h33 : (s : ℕ) * 120 + q < 1140
  · exact x2hMulCheck4_33 s q (by omega) h33
  by_cases h34 : (s : ℕ) * 120 + q < 1170
  · exact x2hMulCheck4_34 s q (by omega) h34
  by_cases h35 : (s : ℕ) * 120 + q < 1200
  · exact x2hMulCheck4_35 s q (by omega) h35
  by_cases h36 : (s : ℕ) * 120 + q < 1230
  · exact x2hMulCheck4_36 s q (by omega) h36
  by_cases h37 : (s : ℕ) * 120 + q < 1260
  · exact x2hMulCheck4_37 s q (by omega) h37
  by_cases h38 : (s : ℕ) * 120 + q < 1290
  · exact x2hMulCheck4_38 s q (by omega) h38
  by_cases h39 : (s : ℕ) * 120 + q < 1320
  · exact x2hMulCheck4_39 s q (by omega) h39
  by_cases h40 : (s : ℕ) * 120 + q < 1350
  · exact x2hMulCheck4_40 s q (by omega) h40
  by_cases h41 : (s : ℕ) * 120 + q < 1380
  · exact x2hMulCheck4_41 s q (by omega) h41
  by_cases h42 : (s : ℕ) * 120 + q < 1410
  · exact x2hMulCheck4_42 s q (by omega) h42
  · exact x2hMulCheck4_43 s q (by omega) (by omega)

theorem x2hMulCheck5 (s : Fin 12) (q : Fin 120) :
    x2hA5 (x2hLMul s q) = x2hA5 (x2hSpecial s) * x2hA5 q := by
  by_cases hs0 : s = 0
  · subst hs0
    rw [x2hLMul0, x2hIdCheck5, Matrix.one_mul]
  have hs : (s : ℕ) ≠ 0 := fun h => hs0 (Fin.ext h)
  have hs' := s.isLt
  have hq := q.isLt
  by_cases h0 : (s : ℕ) * 120 + q < 180
  · exact x2hMulCheck5_0 s q (by omega) h0
  by_cases h1 : (s : ℕ) * 120 + q < 240
  · exact x2hMulCheck5_1 s q (by omega) h1
  by_cases h2 : (s : ℕ) * 120 + q < 300
  · exact x2hMulCheck5_2 s q (by omega) h2
  by_cases h3 : (s : ℕ) * 120 + q < 360
  · exact x2hMulCheck5_3 s q (by omega) h3
  by_cases h4 : (s : ℕ) * 120 + q < 420
  · exact x2hMulCheck5_4 s q (by omega) h4
  by_cases h5 : (s : ℕ) * 120 + q < 480
  · exact x2hMulCheck5_5 s q (by omega) h5
  by_cases h6 : (s : ℕ) * 120 + q < 540
  · exact x2hMulCheck5_6 s q (by omega) h6
  by_cases h7 : (s : ℕ) * 120 + q < 600
  · exact x2hMulCheck5_7 s q (by omega) h7
  by_cases h8 : (s : ℕ) * 120 + q < 660
  · exact x2hMulCheck5_8 s q (by omega) h8
  by_cases h9 : (s : ℕ) * 120 + q < 720
  · exact x2hMulCheck5_9 s q (by omega) h9
  by_cases h10 : (s : ℕ) * 120 + q < 780
  · exact x2hMulCheck5_10 s q (by omega) h10
  by_cases h11 : (s : ℕ) * 120 + q < 840
  · exact x2hMulCheck5_11 s q (by omega) h11
  by_cases h12 : (s : ℕ) * 120 + q < 900
  · exact x2hMulCheck5_12 s q (by omega) h12
  by_cases h13 : (s : ℕ) * 120 + q < 960
  · exact x2hMulCheck5_13 s q (by omega) h13
  by_cases h14 : (s : ℕ) * 120 + q < 1020
  · exact x2hMulCheck5_14 s q (by omega) h14
  by_cases h15 : (s : ℕ) * 120 + q < 1080
  · exact x2hMulCheck5_15 s q (by omega) h15
  by_cases h16 : (s : ℕ) * 120 + q < 1140
  · exact x2hMulCheck5_16 s q (by omega) h16
  by_cases h17 : (s : ℕ) * 120 + q < 1200
  · exact x2hMulCheck5_17 s q (by omega) h17
  by_cases h18 : (s : ℕ) * 120 + q < 1260
  · exact x2hMulCheck5_18 s q (by omega) h18
  by_cases h19 : (s : ℕ) * 120 + q < 1320
  · exact x2hMulCheck5_19 s q (by omega) h19
  by_cases h20 : (s : ℕ) * 120 + q < 1380
  · exact x2hMulCheck5_20 s q (by omega) h20
  · exact x2hMulCheck5_21 s q (by omega) (by omega)

theorem x2hMulCheck6 (s : Fin 12) (q : Fin 120) :
    x2hA6 (x2hLMul s q) = x2hA6 (x2hSpecial s) * x2hA6 q := by
  by_cases hs0 : s = 0
  · subst hs0
    rw [x2hLMul0, x2hIdCheck6, Matrix.one_mul]
  have hs : (s : ℕ) ≠ 0 := fun h => hs0 (Fin.ext h)
  have hs' := s.isLt
  have hq := q.isLt
  by_cases h0 : (s : ℕ) * 120 + q < 180
  · exact x2hMulCheck6_0 s q (by omega) h0
  by_cases h1 : (s : ℕ) * 120 + q < 240
  · exact x2hMulCheck6_1 s q (by omega) h1
  by_cases h2 : (s : ℕ) * 120 + q < 300
  · exact x2hMulCheck6_2 s q (by omega) h2
  by_cases h3 : (s : ℕ) * 120 + q < 360
  · exact x2hMulCheck6_3 s q (by omega) h3
  by_cases h4 : (s : ℕ) * 120 + q < 420
  · exact x2hMulCheck6_4 s q (by omega) h4
  by_cases h5 : (s : ℕ) * 120 + q < 480
  · exact x2hMulCheck6_5 s q (by omega) h5
  by_cases h6 : (s : ℕ) * 120 + q < 540
  · exact x2hMulCheck6_6 s q (by omega) h6
  by_cases h7 : (s : ℕ) * 120 + q < 600
  · exact x2hMulCheck6_7 s q (by omega) h7
  by_cases h8 : (s : ℕ) * 120 + q < 660
  · exact x2hMulCheck6_8 s q (by omega) h8
  by_cases h9 : (s : ℕ) * 120 + q < 720
  · exact x2hMulCheck6_9 s q (by omega) h9
  by_cases h10 : (s : ℕ) * 120 + q < 780
  · exact x2hMulCheck6_10 s q (by omega) h10
  by_cases h11 : (s : ℕ) * 120 + q < 840
  · exact x2hMulCheck6_11 s q (by omega) h11
  by_cases h12 : (s : ℕ) * 120 + q < 900
  · exact x2hMulCheck6_12 s q (by omega) h12
  by_cases h13 : (s : ℕ) * 120 + q < 960
  · exact x2hMulCheck6_13 s q (by omega) h13
  by_cases h14 : (s : ℕ) * 120 + q < 1020
  · exact x2hMulCheck6_14 s q (by omega) h14
  by_cases h15 : (s : ℕ) * 120 + q < 1080
  · exact x2hMulCheck6_15 s q (by omega) h15
  by_cases h16 : (s : ℕ) * 120 + q < 1140
  · exact x2hMulCheck6_16 s q (by omega) h16
  by_cases h17 : (s : ℕ) * 120 + q < 1200
  · exact x2hMulCheck6_17 s q (by omega) h17
  by_cases h18 : (s : ℕ) * 120 + q < 1260
  · exact x2hMulCheck6_18 s q (by omega) h18
  by_cases h19 : (s : ℕ) * 120 + q < 1320
  · exact x2hMulCheck6_19 s q (by omega) h19
  by_cases h20 : (s : ℕ) * 120 + q < 1380
  · exact x2hMulCheck6_20 s q (by omega) h20
  · exact x2hMulCheck6_21 s q (by omega) (by omega)

end ThreeCopyQutritWerner.X2Sites
