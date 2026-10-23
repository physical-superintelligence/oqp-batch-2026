module

public import ThreeCopyQutritWerner.CertificateX2HKeysTranspCheck0
public import ThreeCopyQutritWerner.CertificateX2HKeysTranspCheck1
public import ThreeCopyQutritWerner.CertificateX2HKeysTranspCheck2
public import ThreeCopyQutritWerner.CertificateX2HKeysTranspCheck3
public import ThreeCopyQutritWerner.CertificateX2HKeysTranspCheck4
public import ThreeCopyQutritWerner.CertificateX2HKeysTranspCheck5
public import ThreeCopyQutritWerner.CertificateX2HKeysTranspCheck6
public import ThreeCopyQutritWerner.CertificateX2HKeysTranspCheck7
public import ThreeCopyQutritWerner.CertificateX2HKeysTranspCheck8
public import ThreeCopyQutritWerner.CertificateX2HKeysTranspCheck9
public import ThreeCopyQutritWerner.CertificateX2HKeysTranspCheck10
public import ThreeCopyQutritWerner.CertificateX2HKeysTranspCheck11
public import ThreeCopyQutritWerner.CertificateX2HKeysTranspCheck12
public import ThreeCopyQutritWerner.CertificateX2HKeysTranspCheck13
public import ThreeCopyQutritWerner.CertificateX2HKeysTranspCheck14
public import ThreeCopyQutritWerner.CertificateX2HKeysTranspCheck15
public import ThreeCopyQutritWerner.CertificateX2HKeysTranspCheck16
public import ThreeCopyQutritWerner.CertificateX2HKeysTranspCheck17
public import ThreeCopyQutritWerner.CertificateX2HKeysTranspCheck18
public import ThreeCopyQutritWerner.CertificateX2HKeysTranspCheck19
public import ThreeCopyQutritWerner.CertificateX2HKeysTranspCheck20

@[expose] public section


/-! `keyCheck b = true` for every h key (dispatch). -/

namespace ThreeCopyQutritWerner.X2Sites

theorem keyCheck_all (b : x2Key 0) : keyCheck b = true := by
  by_cases h0 : (b : ℕ) < 47
  · exact x2hKeyCheck_0 b (by omega) h0
  by_cases h1 : (b : ℕ) < 50
  · exact x2hKeyCheck_1 b (by omega) h1
  by_cases h2 : (b : ℕ) < 51
  · exact x2hKeyCheck_2 b (by omega) h2
  by_cases h3 : (b : ℕ) < 52
  · exact x2hKeyCheck_3 b (by omega) h3
  by_cases h4 : (b : ℕ) < 53
  · exact x2hKeyCheck_4 b (by omega) h4
  by_cases h5 : (b : ℕ) < 56
  · exact x2hKeyCheck_5 b (by omega) h5
  by_cases h6 : (b : ℕ) < 64
  · exact x2hKeyCheck_6 b (by omega) h6
  by_cases h7 : (b : ℕ) < 74
  · exact x2hKeyCheck_7 b (by omega) h7
  by_cases h8 : (b : ℕ) < 75
  · exact x2hKeyCheck_8 b (by omega) h8
  by_cases h9 : (b : ℕ) < 76
  · exact x2hKeyCheck_9 b (by omega) h9
  by_cases h10 : (b : ℕ) < 77
  · exact x2hKeyCheck_10 b (by omega) h10
  by_cases h11 : (b : ℕ) < 78
  · exact x2hKeyCheck_11 b (by omega) h11
  by_cases h12 : (b : ℕ) < 81
  · exact x2hKeyCheck_12 b (by omega) h12
  by_cases h13 : (b : ℕ) < 89
  · exact x2hKeyCheck_13 b (by omega) h13
  by_cases h14 : (b : ℕ) < 91
  · exact x2hKeyCheck_14 b (by omega) h14
  by_cases h15 : (b : ℕ) < 92
  · exact x2hKeyCheck_15 b (by omega) h15
  by_cases h16 : (b : ℕ) < 93
  · exact x2hKeyCheck_16 b (by omega) h16
  by_cases h17 : (b : ℕ) < 94
  · exact x2hKeyCheck_17 b (by omega) h17
  by_cases h18 : (b : ℕ) < 95
  · exact x2hKeyCheck_18 b (by omega) h18
  by_cases h19 : (b : ℕ) < 98
  · exact x2hKeyCheck_19 b (by omega) h19
  by_cases h20 : (b : ℕ) < 100
  · exact x2hKeyCheck_20 b (by omega) h20
  by_cases h21 : (b : ℕ) < 101
  · exact x2hKeyCheck_21 b (by omega) h21
  by_cases h22 : (b : ℕ) < 102
  · exact x2hKeyCheck_22 b (by omega) h22
  by_cases h23 : (b : ℕ) < 103
  · exact x2hKeyCheck_23 b (by omega) h23
  by_cases h24 : (b : ℕ) < 104
  · exact x2hKeyCheck_24 b (by omega) h24
  by_cases h25 : (b : ℕ) < 105
  · exact x2hKeyCheck_25 b (by omega) h25
  by_cases h26 : (b : ℕ) < 106
  · exact x2hKeyCheck_26 b (by omega) h26
  by_cases h27 : (b : ℕ) < 107
  · exact x2hKeyCheck_27 b (by omega) h27
  by_cases h28 : (b : ℕ) < 108
  · exact x2hKeyCheck_28 b (by omega) h28
  by_cases h29 : (b : ℕ) < 109
  · exact x2hKeyCheck_29 b (by omega) h29
  by_cases h30 : (b : ℕ) < 110
  · exact x2hKeyCheck_30 b (by omega) h30
  by_cases h31 : (b : ℕ) < 111
  · exact x2hKeyCheck_31 b (by omega) h31
  by_cases h32 : (b : ℕ) < 112
  · exact x2hKeyCheck_32 b (by omega) h32
  by_cases h33 : (b : ℕ) < 114
  · exact x2hKeyCheck_33 b (by omega) h33
  by_cases h34 : (b : ℕ) < 115
  · exact x2hKeyCheck_34 b (by omega) h34
  by_cases h35 : (b : ℕ) < 116
  · exact x2hKeyCheck_35 b (by omega) h35
  by_cases h36 : (b : ℕ) < 117
  · exact x2hKeyCheck_36 b (by omega) h36
  by_cases h37 : (b : ℕ) < 118
  · exact x2hKeyCheck_37 b (by omega) h37
  by_cases h38 : (b : ℕ) < 119
  · exact x2hKeyCheck_38 b (by omega) h38
  by_cases h39 : (b : ℕ) < 121
  · exact x2hKeyCheck_39 b (by omega) h39
  · exact x2hKeyCheck_40 b (by omega) b.isLt

end ThreeCopyQutritWerner.X2Sites
