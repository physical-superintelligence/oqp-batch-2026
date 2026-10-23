module

public import ThreeCopyQutritWerner.CertificateX2InputJChkD0
public import ThreeCopyQutritWerner.CertificateX2InputJChkD1
public import ThreeCopyQutritWerner.CertificateX2InputJChkD2
public import ThreeCopyQutritWerner.CertificateX2InputJChkD3
public import ThreeCopyQutritWerner.CertificateX2InputJChkD4
public import ThreeCopyQutritWerner.CertificateX2InputJChkD5
public import ThreeCopyQutritWerner.CertificateX2InputJInv

@[expose] public section


/-! Stabilizer invariance of the input blocks of EVERY key of the source
sectors 1, 2 (degree 1 and 2), for every source `N`, and the collapse of the full tensor on sorted type
triples for the concrete data. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

open scoped BigOperators

namespace ThreeCopyQutritWerner.X2

theorem x2JK2_1_106 : x2JKeyOK2 1 ⟨106, by decide⟩ = true := by
  apply x2JKeyOK2_of_cols
  intro c hc
  have hsz : x2KeySize 1 ⟨106, by decide⟩ = 39 := by decide
  rw [hsz] at hc
  rcases Nat.lt_or_ge c 17 with h0 | h0
  · exact x2JColRangeOK2_mem _ _ 0 17 c x2JD_1_106_0_17 (by omega) (by omega)
  rcases Nat.lt_or_ge c 34 with h1 | h1
  · exact x2JColRangeOK2_mem _ _ 17 17 c x2JD_1_106_17_17 (by omega) (by omega)
  exact x2JColRangeOK2_mem _ _ 34 5 c x2JD_1_106_34_5 (by omega) (by omega)

theorem x2JK2_1_131 : x2JKeyOK2 1 ⟨131, by decide⟩ = true := by
  apply x2JKeyOK2_of_cols
  intro c hc
  have hsz : x2KeySize 1 ⟨131, by decide⟩ = 19 := by decide
  rw [hsz] at hc
  exact x2JColRangeOK2_mem _ _ 0 19 c x2JD_1_131_0_19 (by omega) (by omega)

theorem x2JK2_1_149 : x2JKeyOK2 1 ⟨149, by decide⟩ = true := by
  apply x2JKeyOK2_of_cols
  intro c hc
  have hsz : x2KeySize 1 ⟨149, by decide⟩ = 18 := by decide
  rw [hsz] at hc
  exact x2JColRangeOK2_mem _ _ 0 18 c x2JD_1_149_0_18 (by omega) (by omega)

theorem x2JK2_1_161 : x2JKeyOK2 1 ⟨161, by decide⟩ = true := by
  apply x2JKeyOK2_of_cols
  intro c hc
  have hsz : x2KeySize 1 ⟨161, by decide⟩ = 273 := by decide
  rw [hsz] at hc
  rcases Nat.lt_or_ge c 2 with h0 | h0
  · exact x2JColRangeOK2_mem _ _ 0 2 c x2JD_1_161_0_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 4 with h1 | h1
  · exact x2JColRangeOK2_mem _ _ 2 2 c x2JD_1_161_2_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 6 with h2 | h2
  · exact x2JColRangeOK2_mem _ _ 4 2 c x2JD_1_161_4_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 8 with h3 | h3
  · exact x2JColRangeOK2_mem _ _ 6 2 c x2JD_1_161_6_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 10 with h4 | h4
  · exact x2JColRangeOK2_mem _ _ 8 2 c x2JD_1_161_8_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 12 with h5 | h5
  · exact x2JColRangeOK2_mem _ _ 10 2 c x2JD_1_161_10_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 14 with h6 | h6
  · exact x2JColRangeOK2_mem _ _ 12 2 c x2JD_1_161_12_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 16 with h7 | h7
  · exact x2JColRangeOK2_mem _ _ 14 2 c x2JD_1_161_14_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 18 with h8 | h8
  · exact x2JColRangeOK2_mem _ _ 16 2 c x2JD_1_161_16_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 20 with h9 | h9
  · exact x2JColRangeOK2_mem _ _ 18 2 c x2JD_1_161_18_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 22 with h10 | h10
  · exact x2JColRangeOK2_mem _ _ 20 2 c x2JD_1_161_20_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 24 with h11 | h11
  · exact x2JColRangeOK2_mem _ _ 22 2 c x2JD_1_161_22_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 26 with h12 | h12
  · exact x2JColRangeOK2_mem _ _ 24 2 c x2JD_1_161_24_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 28 with h13 | h13
  · exact x2JColRangeOK2_mem _ _ 26 2 c x2JD_1_161_26_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 30 with h14 | h14
  · exact x2JColRangeOK2_mem _ _ 28 2 c x2JD_1_161_28_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 32 with h15 | h15
  · exact x2JColRangeOK2_mem _ _ 30 2 c x2JD_1_161_30_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 34 with h16 | h16
  · exact x2JColRangeOK2_mem _ _ 32 2 c x2JD_1_161_32_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 36 with h17 | h17
  · exact x2JColRangeOK2_mem _ _ 34 2 c x2JD_1_161_34_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 38 with h18 | h18
  · exact x2JColRangeOK2_mem _ _ 36 2 c x2JD_1_161_36_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 40 with h19 | h19
  · exact x2JColRangeOK2_mem _ _ 38 2 c x2JD_1_161_38_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 42 with h20 | h20
  · exact x2JColRangeOK2_mem _ _ 40 2 c x2JD_1_161_40_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 44 with h21 | h21
  · exact x2JColRangeOK2_mem _ _ 42 2 c x2JD_1_161_42_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 46 with h22 | h22
  · exact x2JColRangeOK2_mem _ _ 44 2 c x2JD_1_161_44_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 48 with h23 | h23
  · exact x2JColRangeOK2_mem _ _ 46 2 c x2JD_1_161_46_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 50 with h24 | h24
  · exact x2JColRangeOK2_mem _ _ 48 2 c x2JD_1_161_48_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 52 with h25 | h25
  · exact x2JColRangeOK2_mem _ _ 50 2 c x2JD_1_161_50_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 54 with h26 | h26
  · exact x2JColRangeOK2_mem _ _ 52 2 c x2JD_1_161_52_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 56 with h27 | h27
  · exact x2JColRangeOK2_mem _ _ 54 2 c x2JD_1_161_54_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 58 with h28 | h28
  · exact x2JColRangeOK2_mem _ _ 56 2 c x2JD_1_161_56_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 60 with h29 | h29
  · exact x2JColRangeOK2_mem _ _ 58 2 c x2JD_1_161_58_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 62 with h30 | h30
  · exact x2JColRangeOK2_mem _ _ 60 2 c x2JD_1_161_60_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 64 with h31 | h31
  · exact x2JColRangeOK2_mem _ _ 62 2 c x2JD_1_161_62_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 66 with h32 | h32
  · exact x2JColRangeOK2_mem _ _ 64 2 c x2JD_1_161_64_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 68 with h33 | h33
  · exact x2JColRangeOK2_mem _ _ 66 2 c x2JD_1_161_66_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 70 with h34 | h34
  · exact x2JColRangeOK2_mem _ _ 68 2 c x2JD_1_161_68_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 72 with h35 | h35
  · exact x2JColRangeOK2_mem _ _ 70 2 c x2JD_1_161_70_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 74 with h36 | h36
  · exact x2JColRangeOK2_mem _ _ 72 2 c x2JD_1_161_72_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 76 with h37 | h37
  · exact x2JColRangeOK2_mem _ _ 74 2 c x2JD_1_161_74_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 78 with h38 | h38
  · exact x2JColRangeOK2_mem _ _ 76 2 c x2JD_1_161_76_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 80 with h39 | h39
  · exact x2JColRangeOK2_mem _ _ 78 2 c x2JD_1_161_78_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 82 with h40 | h40
  · exact x2JColRangeOK2_mem _ _ 80 2 c x2JD_1_161_80_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 84 with h41 | h41
  · exact x2JColRangeOK2_mem _ _ 82 2 c x2JD_1_161_82_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 86 with h42 | h42
  · exact x2JColRangeOK2_mem _ _ 84 2 c x2JD_1_161_84_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 88 with h43 | h43
  · exact x2JColRangeOK2_mem _ _ 86 2 c x2JD_1_161_86_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 90 with h44 | h44
  · exact x2JColRangeOK2_mem _ _ 88 2 c x2JD_1_161_88_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 92 with h45 | h45
  · exact x2JColRangeOK2_mem _ _ 90 2 c x2JD_1_161_90_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 94 with h46 | h46
  · exact x2JColRangeOK2_mem _ _ 92 2 c x2JD_1_161_92_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 96 with h47 | h47
  · exact x2JColRangeOK2_mem _ _ 94 2 c x2JD_1_161_94_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 98 with h48 | h48
  · exact x2JColRangeOK2_mem _ _ 96 2 c x2JD_1_161_96_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 100 with h49 | h49
  · exact x2JColRangeOK2_mem _ _ 98 2 c x2JD_1_161_98_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 102 with h50 | h50
  · exact x2JColRangeOK2_mem _ _ 100 2 c x2JD_1_161_100_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 104 with h51 | h51
  · exact x2JColRangeOK2_mem _ _ 102 2 c x2JD_1_161_102_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 106 with h52 | h52
  · exact x2JColRangeOK2_mem _ _ 104 2 c x2JD_1_161_104_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 108 with h53 | h53
  · exact x2JColRangeOK2_mem _ _ 106 2 c x2JD_1_161_106_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 110 with h54 | h54
  · exact x2JColRangeOK2_mem _ _ 108 2 c x2JD_1_161_108_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 112 with h55 | h55
  · exact x2JColRangeOK2_mem _ _ 110 2 c x2JD_1_161_110_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 114 with h56 | h56
  · exact x2JColRangeOK2_mem _ _ 112 2 c x2JD_1_161_112_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 116 with h57 | h57
  · exact x2JColRangeOK2_mem _ _ 114 2 c x2JD_1_161_114_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 118 with h58 | h58
  · exact x2JColRangeOK2_mem _ _ 116 2 c x2JD_1_161_116_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 120 with h59 | h59
  · exact x2JColRangeOK2_mem _ _ 118 2 c x2JD_1_161_118_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 122 with h60 | h60
  · exact x2JColRangeOK2_mem _ _ 120 2 c x2JD_1_161_120_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 124 with h61 | h61
  · exact x2JColRangeOK2_mem _ _ 122 2 c x2JD_1_161_122_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 126 with h62 | h62
  · exact x2JColRangeOK2_mem _ _ 124 2 c x2JD_1_161_124_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 128 with h63 | h63
  · exact x2JColRangeOK2_mem _ _ 126 2 c x2JD_1_161_126_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 130 with h64 | h64
  · exact x2JColRangeOK2_mem _ _ 128 2 c x2JD_1_161_128_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 132 with h65 | h65
  · exact x2JColRangeOK2_mem _ _ 130 2 c x2JD_1_161_130_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 134 with h66 | h66
  · exact x2JColRangeOK2_mem _ _ 132 2 c x2JD_1_161_132_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 136 with h67 | h67
  · exact x2JColRangeOK2_mem _ _ 134 2 c x2JD_1_161_134_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 138 with h68 | h68
  · exact x2JColRangeOK2_mem _ _ 136 2 c x2JD_1_161_136_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 140 with h69 | h69
  · exact x2JColRangeOK2_mem _ _ 138 2 c x2JD_1_161_138_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 142 with h70 | h70
  · exact x2JColRangeOK2_mem _ _ 140 2 c x2JD_1_161_140_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 144 with h71 | h71
  · exact x2JColRangeOK2_mem _ _ 142 2 c x2JD_1_161_142_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 146 with h72 | h72
  · exact x2JColRangeOK2_mem _ _ 144 2 c x2JD_1_161_144_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 148 with h73 | h73
  · exact x2JColRangeOK2_mem _ _ 146 2 c x2JD_1_161_146_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 150 with h74 | h74
  · exact x2JColRangeOK2_mem _ _ 148 2 c x2JD_1_161_148_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 152 with h75 | h75
  · exact x2JColRangeOK2_mem _ _ 150 2 c x2JD_1_161_150_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 154 with h76 | h76
  · exact x2JColRangeOK2_mem _ _ 152 2 c x2JD_1_161_152_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 156 with h77 | h77
  · exact x2JColRangeOK2_mem _ _ 154 2 c x2JD_1_161_154_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 158 with h78 | h78
  · exact x2JColRangeOK2_mem _ _ 156 2 c x2JD_1_161_156_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 160 with h79 | h79
  · exact x2JColRangeOK2_mem _ _ 158 2 c x2JD_1_161_158_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 162 with h80 | h80
  · exact x2JColRangeOK2_mem _ _ 160 2 c x2JD_1_161_160_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 164 with h81 | h81
  · exact x2JColRangeOK2_mem _ _ 162 2 c x2JD_1_161_162_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 166 with h82 | h82
  · exact x2JColRangeOK2_mem _ _ 164 2 c x2JD_1_161_164_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 168 with h83 | h83
  · exact x2JColRangeOK2_mem _ _ 166 2 c x2JD_1_161_166_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 170 with h84 | h84
  · exact x2JColRangeOK2_mem _ _ 168 2 c x2JD_1_161_168_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 172 with h85 | h85
  · exact x2JColRangeOK2_mem _ _ 170 2 c x2JD_1_161_170_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 174 with h86 | h86
  · exact x2JColRangeOK2_mem _ _ 172 2 c x2JD_1_161_172_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 176 with h87 | h87
  · exact x2JColRangeOK2_mem _ _ 174 2 c x2JD_1_161_174_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 178 with h88 | h88
  · exact x2JColRangeOK2_mem _ _ 176 2 c x2JD_1_161_176_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 180 with h89 | h89
  · exact x2JColRangeOK2_mem _ _ 178 2 c x2JD_1_161_178_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 182 with h90 | h90
  · exact x2JColRangeOK2_mem _ _ 180 2 c x2JD_1_161_180_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 184 with h91 | h91
  · exact x2JColRangeOK2_mem _ _ 182 2 c x2JD_1_161_182_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 186 with h92 | h92
  · exact x2JColRangeOK2_mem _ _ 184 2 c x2JD_1_161_184_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 188 with h93 | h93
  · exact x2JColRangeOK2_mem _ _ 186 2 c x2JD_1_161_186_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 190 with h94 | h94
  · exact x2JColRangeOK2_mem _ _ 188 2 c x2JD_1_161_188_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 192 with h95 | h95
  · exact x2JColRangeOK2_mem _ _ 190 2 c x2JD_1_161_190_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 194 with h96 | h96
  · exact x2JColRangeOK2_mem _ _ 192 2 c x2JD_1_161_192_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 196 with h97 | h97
  · exact x2JColRangeOK2_mem _ _ 194 2 c x2JD_1_161_194_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 198 with h98 | h98
  · exact x2JColRangeOK2_mem _ _ 196 2 c x2JD_1_161_196_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 200 with h99 | h99
  · exact x2JColRangeOK2_mem _ _ 198 2 c x2JD_1_161_198_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 202 with h100 | h100
  · exact x2JColRangeOK2_mem _ _ 200 2 c x2JD_1_161_200_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 204 with h101 | h101
  · exact x2JColRangeOK2_mem _ _ 202 2 c x2JD_1_161_202_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 206 with h102 | h102
  · exact x2JColRangeOK2_mem _ _ 204 2 c x2JD_1_161_204_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 208 with h103 | h103
  · exact x2JColRangeOK2_mem _ _ 206 2 c x2JD_1_161_206_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 210 with h104 | h104
  · exact x2JColRangeOK2_mem _ _ 208 2 c x2JD_1_161_208_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 212 with h105 | h105
  · exact x2JColRangeOK2_mem _ _ 210 2 c x2JD_1_161_210_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 214 with h106 | h106
  · exact x2JColRangeOK2_mem _ _ 212 2 c x2JD_1_161_212_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 216 with h107 | h107
  · exact x2JColRangeOK2_mem _ _ 214 2 c x2JD_1_161_214_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 218 with h108 | h108
  · exact x2JColRangeOK2_mem _ _ 216 2 c x2JD_1_161_216_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 220 with h109 | h109
  · exact x2JColRangeOK2_mem _ _ 218 2 c x2JD_1_161_218_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 222 with h110 | h110
  · exact x2JColRangeOK2_mem _ _ 220 2 c x2JD_1_161_220_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 224 with h111 | h111
  · exact x2JColRangeOK2_mem _ _ 222 2 c x2JD_1_161_222_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 226 with h112 | h112
  · exact x2JColRangeOK2_mem _ _ 224 2 c x2JD_1_161_224_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 228 with h113 | h113
  · exact x2JColRangeOK2_mem _ _ 226 2 c x2JD_1_161_226_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 230 with h114 | h114
  · exact x2JColRangeOK2_mem _ _ 228 2 c x2JD_1_161_228_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 232 with h115 | h115
  · exact x2JColRangeOK2_mem _ _ 230 2 c x2JD_1_161_230_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 234 with h116 | h116
  · exact x2JColRangeOK2_mem _ _ 232 2 c x2JD_1_161_232_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 236 with h117 | h117
  · exact x2JColRangeOK2_mem _ _ 234 2 c x2JD_1_161_234_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 238 with h118 | h118
  · exact x2JColRangeOK2_mem _ _ 236 2 c x2JD_1_161_236_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 240 with h119 | h119
  · exact x2JColRangeOK2_mem _ _ 238 2 c x2JD_1_161_238_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 242 with h120 | h120
  · exact x2JColRangeOK2_mem _ _ 240 2 c x2JD_1_161_240_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 244 with h121 | h121
  · exact x2JColRangeOK2_mem _ _ 242 2 c x2JD_1_161_242_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 246 with h122 | h122
  · exact x2JColRangeOK2_mem _ _ 244 2 c x2JD_1_161_244_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 248 with h123 | h123
  · exact x2JColRangeOK2_mem _ _ 246 2 c x2JD_1_161_246_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 250 with h124 | h124
  · exact x2JColRangeOK2_mem _ _ 248 2 c x2JD_1_161_248_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 252 with h125 | h125
  · exact x2JColRangeOK2_mem _ _ 250 2 c x2JD_1_161_250_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 254 with h126 | h126
  · exact x2JColRangeOK2_mem _ _ 252 2 c x2JD_1_161_252_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 256 with h127 | h127
  · exact x2JColRangeOK2_mem _ _ 254 2 c x2JD_1_161_254_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 258 with h128 | h128
  · exact x2JColRangeOK2_mem _ _ 256 2 c x2JD_1_161_256_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 260 with h129 | h129
  · exact x2JColRangeOK2_mem _ _ 258 2 c x2JD_1_161_258_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 262 with h130 | h130
  · exact x2JColRangeOK2_mem _ _ 260 2 c x2JD_1_161_260_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 264 with h131 | h131
  · exact x2JColRangeOK2_mem _ _ 262 2 c x2JD_1_161_262_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 266 with h132 | h132
  · exact x2JColRangeOK2_mem _ _ 264 2 c x2JD_1_161_264_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 268 with h133 | h133
  · exact x2JColRangeOK2_mem _ _ 266 2 c x2JD_1_161_266_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 270 with h134 | h134
  · exact x2JColRangeOK2_mem _ _ 268 2 c x2JD_1_161_268_2 (by omega) (by omega)
  rcases Nat.lt_or_ge c 272 with h135 | h135
  · exact x2JColRangeOK2_mem _ _ 270 2 c x2JD_1_161_270_2 (by omega) (by omega)
  exact x2JColRangeOK2_mem _ _ 272 1 c x2JD_1_161_272_1 (by omega) (by omega)

theorem x2JK2_1_168 : x2JKeyOK2 1 ⟨168, by decide⟩ = true := by
  apply x2JKeyOK2_of_cols
  intro c hc
  have hsz : x2KeySize 1 ⟨168, by decide⟩ = 12 := by decide
  rw [hsz] at hc
  exact x2JColRangeOK2_mem _ _ 0 12 c x2JD_1_168_0_12 (by omega) (by omega)

theorem x2Deg2_keys_1 : ∀ k : x2Key 1, x2KeyDegree 1 k = 2 → k.val = 106 ∨ k.val = 131 ∨ k.val = 149 ∨ k.val = 161 ∨ k.val = 168 := by
  decide +kernel

theorem x2Deg2_types_1 : ∀ k : x2Key 1, x2KeyDegree 1 k = 2 →
    x2KeyTypes 1 k 0 = x2KeyTypes 1 k 1 ∧ x2KeyTypes 1 k 1 = x2KeyTypes 1 k 2 := by
  decide +kernel

theorem x2JKeyOK2_all_1 : ∀ k : x2Key 1, x2KeyDegree 1 k = 2 → x2JKeyOK2 1 k = true := by
  intro k hk
  have h := x2Deg2_keys_1 k hk
  obtain ⟨kv, hkv⟩ := k
  rcases h with h0 | h1 | h2 | h3 | h4
  · obtain rfl : kv = 106 := h0
    exact x2JK2_1_106
  · obtain rfl : kv = 131 := h1
    exact x2JK2_1_131
  · obtain rfl : kv = 149 := h2
    exact x2JK2_1_149
  · obtain rfl : kv = 161 := h3
    exact x2JK2_1_161
  · obtain rfl : kv = 168 := h4
    exact x2JK2_1_168

theorem x2JK2_2_29 : x2JKeyOK2 2 ⟨29, by decide⟩ = true := by
  apply x2JKeyOK2_of_cols
  intro c hc
  have hsz : x2KeySize 2 ⟨29, by decide⟩ = 2 := by decide
  rw [hsz] at hc
  exact x2JColRangeOK2_mem _ _ 0 2 c x2JD_2_29_0_2 (by omega) (by omega)

theorem x2JK2_2_61 : x2JKeyOK2 2 ⟨61, by decide⟩ = true := by
  apply x2JKeyOK2_of_cols
  intro c hc
  have hsz : x2KeySize 2 ⟨61, by decide⟩ = 3 := by decide
  rw [hsz] at hc
  exact x2JColRangeOK2_mem _ _ 0 3 c x2JD_2_61_0_3 (by omega) (by omega)

theorem x2JK2_2_85 : x2JKeyOK2 2 ⟨85, by decide⟩ = true := by
  apply x2JKeyOK2_of_cols
  intro c hc
  have hsz : x2KeySize 2 ⟨85, by decide⟩ = 4 := by decide
  rw [hsz] at hc
  exact x2JColRangeOK2_mem _ _ 0 4 c x2JD_2_85_0_4 (by omega) (by omega)

theorem x2JK2_2_103 : x2JKeyOK2 2 ⟨103, by decide⟩ = true := by
  apply x2JKeyOK2_of_cols
  intro c hc
  have hsz : x2KeySize 2 ⟨103, by decide⟩ = 95 := by decide
  rw [hsz] at hc
  rcases Nat.lt_or_ge c 3 with h0 | h0
  · exact x2JColRangeOK2_mem _ _ 0 3 c x2JD_2_103_0_3 (by omega) (by omega)
  rcases Nat.lt_or_ge c 6 with h1 | h1
  · exact x2JColRangeOK2_mem _ _ 3 3 c x2JD_2_103_3_3 (by omega) (by omega)
  rcases Nat.lt_or_ge c 9 with h2 | h2
  · exact x2JColRangeOK2_mem _ _ 6 3 c x2JD_2_103_6_3 (by omega) (by omega)
  rcases Nat.lt_or_ge c 12 with h3 | h3
  · exact x2JColRangeOK2_mem _ _ 9 3 c x2JD_2_103_9_3 (by omega) (by omega)
  rcases Nat.lt_or_ge c 15 with h4 | h4
  · exact x2JColRangeOK2_mem _ _ 12 3 c x2JD_2_103_12_3 (by omega) (by omega)
  rcases Nat.lt_or_ge c 18 with h5 | h5
  · exact x2JColRangeOK2_mem _ _ 15 3 c x2JD_2_103_15_3 (by omega) (by omega)
  rcases Nat.lt_or_ge c 21 with h6 | h6
  · exact x2JColRangeOK2_mem _ _ 18 3 c x2JD_2_103_18_3 (by omega) (by omega)
  rcases Nat.lt_or_ge c 24 with h7 | h7
  · exact x2JColRangeOK2_mem _ _ 21 3 c x2JD_2_103_21_3 (by omega) (by omega)
  rcases Nat.lt_or_ge c 27 with h8 | h8
  · exact x2JColRangeOK2_mem _ _ 24 3 c x2JD_2_103_24_3 (by omega) (by omega)
  rcases Nat.lt_or_ge c 30 with h9 | h9
  · exact x2JColRangeOK2_mem _ _ 27 3 c x2JD_2_103_27_3 (by omega) (by omega)
  rcases Nat.lt_or_ge c 33 with h10 | h10
  · exact x2JColRangeOK2_mem _ _ 30 3 c x2JD_2_103_30_3 (by omega) (by omega)
  rcases Nat.lt_or_ge c 36 with h11 | h11
  · exact x2JColRangeOK2_mem _ _ 33 3 c x2JD_2_103_33_3 (by omega) (by omega)
  rcases Nat.lt_or_ge c 39 with h12 | h12
  · exact x2JColRangeOK2_mem _ _ 36 3 c x2JD_2_103_36_3 (by omega) (by omega)
  rcases Nat.lt_or_ge c 42 with h13 | h13
  · exact x2JColRangeOK2_mem _ _ 39 3 c x2JD_2_103_39_3 (by omega) (by omega)
  rcases Nat.lt_or_ge c 45 with h14 | h14
  · exact x2JColRangeOK2_mem _ _ 42 3 c x2JD_2_103_42_3 (by omega) (by omega)
  rcases Nat.lt_or_ge c 48 with h15 | h15
  · exact x2JColRangeOK2_mem _ _ 45 3 c x2JD_2_103_45_3 (by omega) (by omega)
  rcases Nat.lt_or_ge c 51 with h16 | h16
  · exact x2JColRangeOK2_mem _ _ 48 3 c x2JD_2_103_48_3 (by omega) (by omega)
  rcases Nat.lt_or_ge c 54 with h17 | h17
  · exact x2JColRangeOK2_mem _ _ 51 3 c x2JD_2_103_51_3 (by omega) (by omega)
  rcases Nat.lt_or_ge c 57 with h18 | h18
  · exact x2JColRangeOK2_mem _ _ 54 3 c x2JD_2_103_54_3 (by omega) (by omega)
  rcases Nat.lt_or_ge c 60 with h19 | h19
  · exact x2JColRangeOK2_mem _ _ 57 3 c x2JD_2_103_57_3 (by omega) (by omega)
  rcases Nat.lt_or_ge c 63 with h20 | h20
  · exact x2JColRangeOK2_mem _ _ 60 3 c x2JD_2_103_60_3 (by omega) (by omega)
  rcases Nat.lt_or_ge c 66 with h21 | h21
  · exact x2JColRangeOK2_mem _ _ 63 3 c x2JD_2_103_63_3 (by omega) (by omega)
  rcases Nat.lt_or_ge c 69 with h22 | h22
  · exact x2JColRangeOK2_mem _ _ 66 3 c x2JD_2_103_66_3 (by omega) (by omega)
  rcases Nat.lt_or_ge c 72 with h23 | h23
  · exact x2JColRangeOK2_mem _ _ 69 3 c x2JD_2_103_69_3 (by omega) (by omega)
  rcases Nat.lt_or_ge c 75 with h24 | h24
  · exact x2JColRangeOK2_mem _ _ 72 3 c x2JD_2_103_72_3 (by omega) (by omega)
  rcases Nat.lt_or_ge c 78 with h25 | h25
  · exact x2JColRangeOK2_mem _ _ 75 3 c x2JD_2_103_75_3 (by omega) (by omega)
  rcases Nat.lt_or_ge c 81 with h26 | h26
  · exact x2JColRangeOK2_mem _ _ 78 3 c x2JD_2_103_78_3 (by omega) (by omega)
  rcases Nat.lt_or_ge c 84 with h27 | h27
  · exact x2JColRangeOK2_mem _ _ 81 3 c x2JD_2_103_81_3 (by omega) (by omega)
  rcases Nat.lt_or_ge c 87 with h28 | h28
  · exact x2JColRangeOK2_mem _ _ 84 3 c x2JD_2_103_84_3 (by omega) (by omega)
  rcases Nat.lt_or_ge c 90 with h29 | h29
  · exact x2JColRangeOK2_mem _ _ 87 3 c x2JD_2_103_87_3 (by omega) (by omega)
  rcases Nat.lt_or_ge c 93 with h30 | h30
  · exact x2JColRangeOK2_mem _ _ 90 3 c x2JD_2_103_90_3 (by omega) (by omega)
  exact x2JColRangeOK2_mem _ _ 93 2 c x2JD_2_103_93_2 (by omega) (by omega)

theorem x2JK2_2_115 : x2JKeyOK2 2 ⟨115, by decide⟩ = true := by
  apply x2JKeyOK2_of_cols
  intro c hc
  have hsz : x2KeySize 2 ⟨115, by decide⟩ = 30 := by decide
  rw [hsz] at hc
  rcases Nat.lt_or_ge c 12 with h0 | h0
  · exact x2JColRangeOK2_mem _ _ 0 12 c x2JD_2_115_0_12 (by omega) (by omega)
  rcases Nat.lt_or_ge c 24 with h1 | h1
  · exact x2JColRangeOK2_mem _ _ 12 12 c x2JD_2_115_12_12 (by omega) (by omega)
  exact x2JColRangeOK2_mem _ _ 24 6 c x2JD_2_115_24_6 (by omega) (by omega)

theorem x2JK2_2_122 : x2JKeyOK2 2 ⟨122, by decide⟩ = true := by
  apply x2JKeyOK2_of_cols
  intro c hc
  have hsz : x2KeySize 2 ⟨122, by decide⟩ = 38 := by decide
  rw [hsz] at hc
  rcases Nat.lt_or_ge c 9 with h0 | h0
  · exact x2JColRangeOK2_mem _ _ 0 9 c x2JD_2_122_0_9 (by omega) (by omega)
  rcases Nat.lt_or_ge c 18 with h1 | h1
  · exact x2JColRangeOK2_mem _ _ 9 9 c x2JD_2_122_9_9 (by omega) (by omega)
  rcases Nat.lt_or_ge c 27 with h2 | h2
  · exact x2JColRangeOK2_mem _ _ 18 9 c x2JD_2_122_18_9 (by omega) (by omega)
  rcases Nat.lt_or_ge c 36 with h3 | h3
  · exact x2JColRangeOK2_mem _ _ 27 9 c x2JD_2_122_27_9 (by omega) (by omega)
  exact x2JColRangeOK2_mem _ _ 36 2 c x2JD_2_122_36_2 (by omega) (by omega)

theorem x2Deg2_keys_2 : ∀ k : x2Key 2, x2KeyDegree 2 k = 2 → k.val = 29 ∨ k.val = 61 ∨ k.val = 85 ∨ k.val = 103 ∨ k.val = 115 ∨ k.val = 122 := by
  decide +kernel

theorem x2Deg2_types_2 : ∀ k : x2Key 2, x2KeyDegree 2 k = 2 →
    x2KeyTypes 2 k 0 = x2KeyTypes 2 k 1 ∧ x2KeyTypes 2 k 1 = x2KeyTypes 2 k 2 := by
  decide +kernel

theorem x2JKeyOK2_all_2 : ∀ k : x2Key 2, x2KeyDegree 2 k = 2 → x2JKeyOK2 2 k = true := by
  intro k hk
  have h := x2Deg2_keys_2 k hk
  obtain ⟨kv, hkv⟩ := k
  rcases h with h0 | h1 | h2 | h3 | h4 | h5
  · obtain rfl : kv = 29 := h0
    exact x2JK2_2_29
  · obtain rfl : kv = 61 := h1
    exact x2JK2_2_61
  · obtain rfl : kv = 85 := h2
    exact x2JK2_2_85
  · obtain rfl : kv = 103 := h3
    exact x2JK2_2_103
  · obtain rfl : kv = 115 := h4
    exact x2JK2_2_115
  · obtain rfl : kv = 122 := h5
    exact x2JK2_2_122

/-- Stabilizer invariance of the input blocks of every key of the source sectors 1, 2, for every source
`N` (the hypothesis `hinv` of `x2FullTensor_sorted`). -/
theorem x2InputBlock_inv_concrete (s : Fin 3) (hs : s = 1 ∨ s = 2) (N : X2Blocks s) (k : x2Key s) (p : Fin 6)
    (hp : x2KeyTypes s k ∘ x2Perm3 p = x2KeyTypes s k) (a b : Fin 3 → ℕ) :
    x2Lookup (x2InputBlock x2DataConcrete s N k) (a ∘ x2Perm3 p) (b ∘ x2Perm3 p) =
      x2Lookup (x2InputBlock x2DataConcrete s N k) a b := by
  by_cases hdeg : x2KeyDegree s k = 2
  · rcases hs with rfl | rfl
    · exact x2InputBlock_inv_deg2_of_ok 1 N k (x2JKeyOK2_all_1 k hdeg) hdeg (x2Deg2_types_1 k hdeg).1
        (x2Deg2_types_1 k hdeg).2 p hp a b
    · exact x2InputBlock_inv_deg2_of_ok 2 N k (x2JKeyOK2_all_2 k hdeg) hdeg (x2Deg2_types_2 k hdeg).1
        (x2Deg2_types_2 k hdeg).2 p hp a b
  · exact x2InputBlock_inv_deg1_concrete s hs N k hdeg p hp a b

/-- Input stage, step 2 for the concrete data: on a sorted type triple the full tensor of a source of
sector 1 or 2 is the plain sum of the input-block lookups of the keys of that triple. -/
theorem x2FullTensor_sorted_concrete (s : Fin 3) (hs : s = 1 ∨ s = 2) (N : X2Blocks s) (t : Fin 3 → Fin 8)
    (a b : Fin 3 → ℕ) (ht : x2Sorted t) :
    x2FullTensor x2DataConcrete s N t a b =
      ∑ k : x2Key s, if x2KeyTypes s k = t then x2Lookup (x2InputBlock x2DataConcrete s N k) a b else 0 := by
  have hkeys : ∀ k : x2Key s, x2Sorted (x2KeyTypes s k) := by
    rcases hs with rfl | rfl
    · exact x2KeyTypes_sorted_1
    · exact x2KeyTypes_sorted_2
  refine x2FullTensor_sorted x2DataConcrete s N t a b ht hkeys ?_
  intro k hk p hp
  subst hk
  exact x2InputBlock_inv_concrete s hs N k p hp a b

end ThreeCopyQutritWerner.X2
