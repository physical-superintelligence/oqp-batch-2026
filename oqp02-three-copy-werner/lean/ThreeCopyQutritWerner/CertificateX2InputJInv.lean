module

public import ThreeCopyQutritWerner.CertificateX2InputJChk0
public import ThreeCopyQutritWerner.CertificateX2InputJChk1
public import ThreeCopyQutritWerner.CertificateX2InputJChk2
public import ThreeCopyQutritWerner.CertificateX2InputJChk3
public import ThreeCopyQutritWerner.CertificateX2InputJChk4
public import ThreeCopyQutritWerner.CertificateX2InputJChk5
public import ThreeCopyQutritWerner.CertificateX2InputJChk6
public import ThreeCopyQutritWerner.CertificateX2InputJChk7
public import ThreeCopyQutritWerner.CertificateX2InputJChk8
public import ThreeCopyQutritWerner.CertificateX2InputJChk9
public import ThreeCopyQutritWerner.CertificateX2InputJChk10
public import ThreeCopyQutritWerner.CertificateX2InputJChk11

@[expose] public section


/-! The images' sign laws for all degree-1 keys of the source sectors, and
the stabilizer invariance of their input blocks. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThreeCopyQutritWerner.X2

theorem x2JK_1_112 : x2JKeyOK 1 ⟨112, by decide⟩ = true := by
  apply x2JKeyOK_of_cols
  intro c hc
  have hsz : x2KeySize 1 ⟨112, by decide⟩ = 102 := by decide
  rw [hsz] at hc
  rcases Nat.lt_or_ge c 51 with h0 | h0
  · exact x2JColRangeOK_mem _ _ 0 51 c x2JC_1_112_0_51 (by omega) (by omega)
  exact x2JColRangeOK_mem _ _ 51 51 c x2JC_1_112_51_51 (by omega) (by omega)

theorem x2JK_1_124 : x2JKeyOK 1 ⟨124, by decide⟩ = true := by
  apply x2JKeyOK_of_cols
  intro c hc
  have hsz : x2KeySize 1 ⟨124, by decide⟩ = 225 := by decide
  rw [hsz] at hc
  rcases Nat.lt_or_ge c 32 with h0 | h0
  · exact x2JColRangeOK_mem _ _ 0 32 c x2JC_1_124_0_32 (by omega) (by omega)
  rcases Nat.lt_or_ge c 64 with h1 | h1
  · exact x2JColRangeOK_mem _ _ 32 32 c x2JC_1_124_32_32 (by omega) (by omega)
  rcases Nat.lt_or_ge c 96 with h2 | h2
  · exact x2JColRangeOK_mem _ _ 64 32 c x2JC_1_124_64_32 (by omega) (by omega)
  rcases Nat.lt_or_ge c 128 with h3 | h3
  · exact x2JColRangeOK_mem _ _ 96 32 c x2JC_1_124_96_32 (by omega) (by omega)
  rcases Nat.lt_or_ge c 160 with h4 | h4
  · exact x2JColRangeOK_mem _ _ 128 32 c x2JC_1_124_128_32 (by omega) (by omega)
  rcases Nat.lt_or_ge c 192 with h5 | h5
  · exact x2JColRangeOK_mem _ _ 160 32 c x2JC_1_124_160_32 (by omega) (by omega)
  rcases Nat.lt_or_ge c 224 with h6 | h6
  · exact x2JColRangeOK_mem _ _ 192 32 c x2JC_1_124_192_32 (by omega) (by omega)
  exact x2JColRangeOK_mem _ _ 224 1 c x2JC_1_124_224_1 (by omega) (by omega)

theorem x2JK_1_125 : x2JKeyOK 1 ⟨125, by decide⟩ = true := by
  apply x2JKeyOK_of_cols
  intro c hc
  have hsz : x2KeySize 1 ⟨125, by decide⟩ = 208 := by decide
  rw [hsz] at hc
  rcases Nat.lt_or_ge c 28 with h0 | h0
  · exact x2JColRangeOK_mem _ _ 0 28 c x2JC_1_125_0_28 (by omega) (by omega)
  rcases Nat.lt_or_ge c 56 with h1 | h1
  · exact x2JColRangeOK_mem _ _ 28 28 c x2JC_1_125_28_28 (by omega) (by omega)
  rcases Nat.lt_or_ge c 84 with h2 | h2
  · exact x2JColRangeOK_mem _ _ 56 28 c x2JC_1_125_56_28 (by omega) (by omega)
  rcases Nat.lt_or_ge c 112 with h3 | h3
  · exact x2JColRangeOK_mem _ _ 84 28 c x2JC_1_125_84_28 (by omega) (by omega)
  rcases Nat.lt_or_ge c 140 with h4 | h4
  · exact x2JColRangeOK_mem _ _ 112 28 c x2JC_1_125_112_28 (by omega) (by omega)
  rcases Nat.lt_or_ge c 168 with h5 | h5
  · exact x2JColRangeOK_mem _ _ 140 28 c x2JC_1_125_140_28 (by omega) (by omega)
  rcases Nat.lt_or_ge c 196 with h6 | h6
  · exact x2JColRangeOK_mem _ _ 168 28 c x2JC_1_125_168_28 (by omega) (by omega)
  exact x2JColRangeOK_mem _ _ 196 12 c x2JC_1_125_196_12 (by omega) (by omega)

theorem x2JK_1_142 : x2JKeyOK 1 ⟨142, by decide⟩ = true := by
  apply x2JKeyOK_of_cols
  intro c hc
  have hsz : x2KeySize 1 ⟨142, by decide⟩ = 180 := by decide
  rw [hsz] at hc
  rcases Nat.lt_or_ge c 41 with h0 | h0
  · exact x2JColRangeOK_mem _ _ 0 41 c x2JC_1_142_0_41 (by omega) (by omega)
  rcases Nat.lt_or_ge c 82 with h1 | h1
  · exact x2JColRangeOK_mem _ _ 41 41 c x2JC_1_142_41_41 (by omega) (by omega)
  rcases Nat.lt_or_ge c 123 with h2 | h2
  · exact x2JColRangeOK_mem _ _ 82 41 c x2JC_1_142_82_41 (by omega) (by omega)
  rcases Nat.lt_or_ge c 164 with h3 | h3
  · exact x2JColRangeOK_mem _ _ 123 41 c x2JC_1_142_123_41 (by omega) (by omega)
  exact x2JColRangeOK_mem _ _ 164 16 c x2JC_1_142_164_16 (by omega) (by omega)

theorem x2JK_1_143 : x2JKeyOK 1 ⟨143, by decide⟩ = true := by
  apply x2JKeyOK_of_cols
  intro c hc
  have hsz : x2KeySize 1 ⟨143, by decide⟩ = 157 := by decide
  rw [hsz] at hc
  rcases Nat.lt_or_ge c 36 with h0 | h0
  · exact x2JColRangeOK_mem _ _ 0 36 c x2JC_1_143_0_36 (by omega) (by omega)
  rcases Nat.lt_or_ge c 72 with h1 | h1
  · exact x2JColRangeOK_mem _ _ 36 36 c x2JC_1_143_36_36 (by omega) (by omega)
  rcases Nat.lt_or_ge c 108 with h2 | h2
  · exact x2JColRangeOK_mem _ _ 72 36 c x2JC_1_143_72_36 (by omega) (by omega)
  rcases Nat.lt_or_ge c 144 with h3 | h3
  · exact x2JColRangeOK_mem _ _ 108 36 c x2JC_1_143_108_36 (by omega) (by omega)
  exact x2JColRangeOK_mem _ _ 144 13 c x2JC_1_143_144_13 (by omega) (by omega)

theorem x2JK_1_154 : x2JKeyOK 1 ⟨154, by decide⟩ = true := by
  apply x2JKeyOK_of_cols
  intro c hc
  have hsz : x2KeySize 1 ⟨154, by decide⟩ = 174 := by decide
  rw [hsz] at hc
  rcases Nat.lt_or_ge c 41 with h0 | h0
  · exact x2JColRangeOK_mem _ _ 0 41 c x2JC_1_154_0_41 (by omega) (by omega)
  rcases Nat.lt_or_ge c 82 with h1 | h1
  · exact x2JColRangeOK_mem _ _ 41 41 c x2JC_1_154_41_41 (by omega) (by omega)
  rcases Nat.lt_or_ge c 123 with h2 | h2
  · exact x2JColRangeOK_mem _ _ 82 41 c x2JC_1_154_82_41 (by omega) (by omega)
  rcases Nat.lt_or_ge c 164 with h3 | h3
  · exact x2JColRangeOK_mem _ _ 123 41 c x2JC_1_154_123_41 (by omega) (by omega)
  exact x2JColRangeOK_mem _ _ 164 10 c x2JC_1_154_164_10 (by omega) (by omega)

theorem x2JK_1_155 : x2JKeyOK 1 ⟨155, by decide⟩ = true := by
  apply x2JKeyOK_of_cols
  intro c hc
  have hsz : x2KeySize 1 ⟨155, by decide⟩ = 163 := by decide
  rw [hsz] at hc
  rcases Nat.lt_or_ge c 36 with h0 | h0
  · exact x2JColRangeOK_mem _ _ 0 36 c x2JC_1_155_0_36 (by omega) (by omega)
  rcases Nat.lt_or_ge c 72 with h1 | h1
  · exact x2JColRangeOK_mem _ _ 36 36 c x2JC_1_155_36_36 (by omega) (by omega)
  rcases Nat.lt_or_ge c 108 with h2 | h2
  · exact x2JColRangeOK_mem _ _ 72 36 c x2JC_1_155_72_36 (by omega) (by omega)
  rcases Nat.lt_or_ge c 144 with h3 | h3
  · exact x2JColRangeOK_mem _ _ 108 36 c x2JC_1_155_108_36 (by omega) (by omega)
  exact x2JColRangeOK_mem _ _ 144 19 c x2JC_1_155_144_19 (by omega) (by omega)

theorem x2JK_1_159 : x2JKeyOK 1 ⟨159, by decide⟩ = true := by
  apply x2JKeyOK_of_cols
  intro c hc
  have hsz : x2KeySize 1 ⟨159, by decide⟩ = 159 := by decide
  rw [hsz] at hc
  rcases Nat.lt_or_ge c 13 with h0 | h0
  · exact x2JColRangeOK_mem _ _ 0 13 c x2JC_1_159_0_13 (by omega) (by omega)
  rcases Nat.lt_or_ge c 26 with h1 | h1
  · exact x2JColRangeOK_mem _ _ 13 13 c x2JC_1_159_13_13 (by omega) (by omega)
  rcases Nat.lt_or_ge c 39 with h2 | h2
  · exact x2JColRangeOK_mem _ _ 26 13 c x2JC_1_159_26_13 (by omega) (by omega)
  rcases Nat.lt_or_ge c 52 with h3 | h3
  · exact x2JColRangeOK_mem _ _ 39 13 c x2JC_1_159_39_13 (by omega) (by omega)
  rcases Nat.lt_or_ge c 65 with h4 | h4
  · exact x2JColRangeOK_mem _ _ 52 13 c x2JC_1_159_52_13 (by omega) (by omega)
  rcases Nat.lt_or_ge c 78 with h5 | h5
  · exact x2JColRangeOK_mem _ _ 65 13 c x2JC_1_159_65_13 (by omega) (by omega)
  rcases Nat.lt_or_ge c 91 with h6 | h6
  · exact x2JColRangeOK_mem _ _ 78 13 c x2JC_1_159_78_13 (by omega) (by omega)
  rcases Nat.lt_or_ge c 104 with h7 | h7
  · exact x2JColRangeOK_mem _ _ 91 13 c x2JC_1_159_91_13 (by omega) (by omega)
  rcases Nat.lt_or_ge c 117 with h8 | h8
  · exact x2JColRangeOK_mem _ _ 104 13 c x2JC_1_159_104_13 (by omega) (by omega)
  rcases Nat.lt_or_ge c 130 with h9 | h9
  · exact x2JColRangeOK_mem _ _ 117 13 c x2JC_1_159_117_13 (by omega) (by omega)
  rcases Nat.lt_or_ge c 143 with h10 | h10
  · exact x2JColRangeOK_mem _ _ 130 13 c x2JC_1_159_130_13 (by omega) (by omega)
  rcases Nat.lt_or_ge c 156 with h11 | h11
  · exact x2JColRangeOK_mem _ _ 143 13 c x2JC_1_159_143_13 (by omega) (by omega)
  exact x2JColRangeOK_mem _ _ 156 3 c x2JC_1_159_156_3 (by omega) (by omega)

theorem x2JK_1_160 : x2JKeyOK 1 ⟨160, by decide⟩ = true := by
  apply x2JKeyOK_of_cols
  intro c hc
  have hsz : x2KeySize 1 ⟨160, by decide⟩ = 114 := by decide
  rw [hsz] at hc
  rcases Nat.lt_or_ge c 7 with h0 | h0
  · exact x2JColRangeOK_mem _ _ 0 7 c x2JC_1_160_0_7 (by omega) (by omega)
  rcases Nat.lt_or_ge c 14 with h1 | h1
  · exact x2JColRangeOK_mem _ _ 7 7 c x2JC_1_160_7_7 (by omega) (by omega)
  rcases Nat.lt_or_ge c 21 with h2 | h2
  · exact x2JColRangeOK_mem _ _ 14 7 c x2JC_1_160_14_7 (by omega) (by omega)
  rcases Nat.lt_or_ge c 28 with h3 | h3
  · exact x2JColRangeOK_mem _ _ 21 7 c x2JC_1_160_21_7 (by omega) (by omega)
  rcases Nat.lt_or_ge c 35 with h4 | h4
  · exact x2JColRangeOK_mem _ _ 28 7 c x2JC_1_160_28_7 (by omega) (by omega)
  rcases Nat.lt_or_ge c 42 with h5 | h5
  · exact x2JColRangeOK_mem _ _ 35 7 c x2JC_1_160_35_7 (by omega) (by omega)
  rcases Nat.lt_or_ge c 49 with h6 | h6
  · exact x2JColRangeOK_mem _ _ 42 7 c x2JC_1_160_42_7 (by omega) (by omega)
  rcases Nat.lt_or_ge c 56 with h7 | h7
  · exact x2JColRangeOK_mem _ _ 49 7 c x2JC_1_160_49_7 (by omega) (by omega)
  rcases Nat.lt_or_ge c 63 with h8 | h8
  · exact x2JColRangeOK_mem _ _ 56 7 c x2JC_1_160_56_7 (by omega) (by omega)
  rcases Nat.lt_or_ge c 70 with h9 | h9
  · exact x2JColRangeOK_mem _ _ 63 7 c x2JC_1_160_63_7 (by omega) (by omega)
  rcases Nat.lt_or_ge c 77 with h10 | h10
  · exact x2JColRangeOK_mem _ _ 70 7 c x2JC_1_160_70_7 (by omega) (by omega)
  rcases Nat.lt_or_ge c 84 with h11 | h11
  · exact x2JColRangeOK_mem _ _ 77 7 c x2JC_1_160_77_7 (by omega) (by omega)
  rcases Nat.lt_or_ge c 91 with h12 | h12
  · exact x2JColRangeOK_mem _ _ 84 7 c x2JC_1_160_84_7 (by omega) (by omega)
  rcases Nat.lt_or_ge c 98 with h13 | h13
  · exact x2JColRangeOK_mem _ _ 91 7 c x2JC_1_160_91_7 (by omega) (by omega)
  rcases Nat.lt_or_ge c 105 with h14 | h14
  · exact x2JColRangeOK_mem _ _ 98 7 c x2JC_1_160_98_7 (by omega) (by omega)
  rcases Nat.lt_or_ge c 112 with h15 | h15
  · exact x2JColRangeOK_mem _ _ 105 7 c x2JC_1_160_105_7 (by omega) (by omega)
  exact x2JColRangeOK_mem _ _ 112 2 c x2JC_1_160_112_2 (by omega) (by omega)

theorem x2JK_1_162 : x2JKeyOK 1 ⟨162, by decide⟩ = true := by
  apply x2JKeyOK_of_cols
  intro c hc
  have hsz : x2KeySize 1 ⟨162, by decide⟩ = 153 := by decide
  rw [hsz] at hc
  rcases Nat.lt_or_ge c 69 with h0 | h0
  · exact x2JColRangeOK_mem _ _ 0 69 c x2JC_1_162_0_69 (by omega) (by omega)
  rcases Nat.lt_or_ge c 138 with h1 | h1
  · exact x2JColRangeOK_mem _ _ 69 69 c x2JC_1_162_69_69 (by omega) (by omega)
  exact x2JColRangeOK_mem _ _ 138 15 c x2JC_1_162_138_15 (by omega) (by omega)

theorem x2JK_1_163 : x2JKeyOK 1 ⟨163, by decide⟩ = true := by
  apply x2JKeyOK_of_cols
  intro c hc
  have hsz : x2KeySize 1 ⟨163, by decide⟩ = 136 := by decide
  rw [hsz] at hc
  rcases Nat.lt_or_ge c 41 with h0 | h0
  · exact x2JColRangeOK_mem _ _ 0 41 c x2JC_1_163_0_41 (by omega) (by omega)
  rcases Nat.lt_or_ge c 82 with h1 | h1
  · exact x2JColRangeOK_mem _ _ 41 41 c x2JC_1_163_41_41 (by omega) (by omega)
  rcases Nat.lt_or_ge c 123 with h2 | h2
  · exact x2JColRangeOK_mem _ _ 82 41 c x2JC_1_163_82_41 (by omega) (by omega)
  exact x2JColRangeOK_mem _ _ 123 13 c x2JC_1_163_123_13 (by omega) (by omega)

theorem x2JKeyOK_all_1 : ∀ k : x2Key 1, x2JKeyOK 1 k = true := by
  intro k
  obtain ⟨kv, hk⟩ := k
  have hk' : kv < 169 := hk
  rcases Nat.lt_or_ge kv 70 with h0 | h0
  · exact x2JKeyRangeOK_mem 1 0 70 x2JR_1_0_70 ⟨kv, hk⟩ (show 0 ≤ kv by omega) (show kv < 0 + 70 by omega)
  rcases Nat.lt_or_ge kv 100 with h1 | h1
  · exact x2JKeyRangeOK_mem 1 70 30 x2JR_1_70_30 ⟨kv, hk⟩ (show 70 ≤ kv by omega) (show kv < 70 + 30 by omega)
  rcases Nat.lt_or_ge kv 105 with h2 | h2
  · exact x2JKeyRangeOK_mem 1 100 5 x2JR_1_100_5 ⟨kv, hk⟩ (show 100 ≤ kv by omega) (show kv < 100 + 5 by omega)
  rcases Nat.lt_or_ge kv 109 with h3 | h3
  · exact x2JKeyRangeOK_mem 1 105 4 x2JR_1_105_4 ⟨kv, hk⟩ (show 105 ≤ kv by omega) (show kv < 105 + 4 by omega)
  rcases Nat.lt_or_ge kv 111 with h4 | h4
  · exact x2JKeyRangeOK_mem 1 109 2 x2JR_1_109_2 ⟨kv, hk⟩ (show 109 ≤ kv by omega) (show kv < 109 + 2 by omega)
  rcases Nat.lt_or_ge kv 112 with h5 | h5
  · exact x2JKeyRangeOK_mem 1 111 1 x2JR_1_111_1 ⟨kv, hk⟩ (show 111 ≤ kv by omega) (show kv < 111 + 1 by omega)
  rcases Nat.lt_or_ge kv 113 with h6 | h6
  · obtain rfl : kv = 112 := by omega
    exact x2JK_1_112
  rcases Nat.lt_or_ge kv 120 with h7 | h7
  · exact x2JKeyRangeOK_mem 1 113 7 x2JR_1_113_7 ⟨kv, hk⟩ (show 113 ≤ kv by omega) (show kv < 113 + 7 by omega)
  rcases Nat.lt_or_ge kv 124 with h8 | h8
  · exact x2JKeyRangeOK_mem 1 120 4 x2JR_1_120_4 ⟨kv, hk⟩ (show 120 ≤ kv by omega) (show kv < 120 + 4 by omega)
  rcases Nat.lt_or_ge kv 125 with h9 | h9
  · obtain rfl : kv = 124 := by omega
    exact x2JK_1_124
  rcases Nat.lt_or_ge kv 126 with h10 | h10
  · obtain rfl : kv = 125 := by omega
    exact x2JK_1_125
  rcases Nat.lt_or_ge kv 135 with h11 | h11
  · exact x2JKeyRangeOK_mem 1 126 9 x2JR_1_126_9 ⟨kv, hk⟩ (show 126 ≤ kv by omega) (show kv < 126 + 9 by omega)
  rcases Nat.lt_or_ge kv 138 with h12 | h12
  · exact x2JKeyRangeOK_mem 1 135 3 x2JR_1_135_3 ⟨kv, hk⟩ (show 135 ≤ kv by omega) (show kv < 135 + 3 by omega)
  rcases Nat.lt_or_ge kv 142 with h13 | h13
  · exact x2JKeyRangeOK_mem 1 138 4 x2JR_1_138_4 ⟨kv, hk⟩ (show 138 ≤ kv by omega) (show kv < 138 + 4 by omega)
  rcases Nat.lt_or_ge kv 143 with h14 | h14
  · obtain rfl : kv = 142 := by omega
    exact x2JK_1_142
  rcases Nat.lt_or_ge kv 144 with h15 | h15
  · obtain rfl : kv = 143 := by omega
    exact x2JK_1_143
  rcases Nat.lt_or_ge kv 151 with h16 | h16
  · exact x2JKeyRangeOK_mem 1 144 7 x2JR_1_144_7 ⟨kv, hk⟩ (show 144 ≤ kv by omega) (show kv < 144 + 7 by omega)
  rcases Nat.lt_or_ge kv 154 with h17 | h17
  · exact x2JKeyRangeOK_mem 1 151 3 x2JR_1_151_3 ⟨kv, hk⟩ (show 151 ≤ kv by omega) (show kv < 151 + 3 by omega)
  rcases Nat.lt_or_ge kv 155 with h18 | h18
  · obtain rfl : kv = 154 := by omega
    exact x2JK_1_154
  rcases Nat.lt_or_ge kv 156 with h19 | h19
  · obtain rfl : kv = 155 := by omega
    exact x2JK_1_155
  rcases Nat.lt_or_ge kv 159 with h20 | h20
  · exact x2JKeyRangeOK_mem 1 156 3 x2JR_1_156_3 ⟨kv, hk⟩ (show 156 ≤ kv by omega) (show kv < 156 + 3 by omega)
  rcases Nat.lt_or_ge kv 160 with h21 | h21
  · obtain rfl : kv = 159 := by omega
    exact x2JK_1_159
  rcases Nat.lt_or_ge kv 161 with h22 | h22
  · obtain rfl : kv = 160 := by omega
    exact x2JK_1_160
  rcases Nat.lt_or_ge kv 162 with h23 | h23
  · exact x2JKeyRangeOK_mem 1 161 1 x2JR_1_161_1 ⟨kv, hk⟩ (show 161 ≤ kv by omega) (show kv < 161 + 1 by omega)
  rcases Nat.lt_or_ge kv 163 with h24 | h24
  · obtain rfl : kv = 162 := by omega
    exact x2JK_1_162
  rcases Nat.lt_or_ge kv 164 with h25 | h25
  · obtain rfl : kv = 163 := by omega
    exact x2JK_1_163
  exact x2JKeyRangeOK_mem 1 164 5 x2JR_1_164_5 ⟨kv, hk⟩ (show 164 ≤ kv by omega) (show kv < 164 + 5 by omega)

theorem x2KeyTypes_sorted_1 : ∀ k : x2Key 1, x2Sorted (x2KeyTypes 1 k) := by
  have h : ∀ k : x2Key 1, x2KeyTypes 1 k 0 ≤ x2KeyTypes 1 k 1 ∧ x2KeyTypes 1 k 1 ≤ x2KeyTypes 1 k 2 := by
    decide +kernel
  exact h

theorem x2JK_2_101 : x2JKeyOK 2 ⟨101, by decide⟩ = true := by
  apply x2JKeyOK_of_cols
  intro c hc
  have hsz : x2KeySize 2 ⟨101, by decide⟩ = 53 := by decide
  rw [hsz] at hc
  rcases Nat.lt_or_ge c 19 with h0 | h0
  · exact x2JColRangeOK_mem _ _ 0 19 c x2JC_2_101_0_19 (by omega) (by omega)
  rcases Nat.lt_or_ge c 38 with h1 | h1
  · exact x2JColRangeOK_mem _ _ 19 19 c x2JC_2_101_19_19 (by omega) (by omega)
  exact x2JColRangeOK_mem _ _ 38 15 c x2JC_2_101_38_15 (by omega) (by omega)

theorem x2JK_2_102 : x2JKeyOK 2 ⟨102, by decide⟩ = true := by
  apply x2JKeyOK_of_cols
  intro c hc
  have hsz : x2KeySize 2 ⟨102, by decide⟩ = 38 := by decide
  rw [hsz] at hc
  rcases Nat.lt_or_ge c 10 with h0 | h0
  · exact x2JColRangeOK_mem _ _ 0 10 c x2JC_2_102_0_10 (by omega) (by omega)
  rcases Nat.lt_or_ge c 20 with h1 | h1
  · exact x2JColRangeOK_mem _ _ 10 10 c x2JC_2_102_10_10 (by omega) (by omega)
  rcases Nat.lt_or_ge c 30 with h2 | h2
  · exact x2JColRangeOK_mem _ _ 20 10 c x2JC_2_102_20_10 (by omega) (by omega)
  exact x2JColRangeOK_mem _ _ 30 8 c x2JC_2_102_30_8 (by omega) (by omega)

theorem x2JK_2_104 : x2JKeyOK 2 ⟨104, by decide⟩ = true := by
  apply x2JKeyOK_of_cols
  intro c hc
  have hsz : x2KeySize 2 ⟨104, by decide⟩ = 104 := by decide
  rw [hsz] at hc
  rcases Nat.lt_or_ge c 88 with h0 | h0
  · exact x2JColRangeOK_mem _ _ 0 88 c x2JC_2_104_0_88 (by omega) (by omega)
  exact x2JColRangeOK_mem _ _ 88 16 c x2JC_2_104_88_16 (by omega) (by omega)

theorem x2JK_2_105 : x2JKeyOK 2 ⟨105, by decide⟩ = true := by
  apply x2JKeyOK_of_cols
  intro c hc
  have hsz : x2KeySize 2 ⟨105, by decide⟩ = 84 := by decide
  rw [hsz] at hc
  rcases Nat.lt_or_ge c 32 with h0 | h0
  · exact x2JColRangeOK_mem _ _ 0 32 c x2JC_2_105_0_32 (by omega) (by omega)
  rcases Nat.lt_or_ge c 64 with h1 | h1
  · exact x2JColRangeOK_mem _ _ 32 32 c x2JC_2_105_32_32 (by omega) (by omega)
  exact x2JColRangeOK_mem _ _ 64 20 c x2JC_2_105_64_20 (by omega) (by omega)

theorem x2JK_2_106 : x2JKeyOK 2 ⟨106, by decide⟩ = true := by
  apply x2JKeyOK_of_cols
  intro c hc
  have hsz : x2KeySize 2 ⟨106, by decide⟩ = 108 := by decide
  rw [hsz] at hc
  rcases Nat.lt_or_ge c 88 with h0 | h0
  · exact x2JColRangeOK_mem _ _ 0 88 c x2JC_2_106_0_88 (by omega) (by omega)
  exact x2JColRangeOK_mem _ _ 88 20 c x2JC_2_106_88_20 (by omega) (by omega)

theorem x2JK_2_107 : x2JKeyOK 2 ⟨107, by decide⟩ = true := by
  apply x2JKeyOK_of_cols
  intro c hc
  have hsz : x2KeySize 2 ⟨107, by decide⟩ = 98 := by decide
  rw [hsz] at hc
  rcases Nat.lt_or_ge c 29 with h0 | h0
  · exact x2JColRangeOK_mem _ _ 0 29 c x2JC_2_107_0_29 (by omega) (by omega)
  rcases Nat.lt_or_ge c 58 with h1 | h1
  · exact x2JColRangeOK_mem _ _ 29 29 c x2JC_2_107_29_29 (by omega) (by omega)
  rcases Nat.lt_or_ge c 87 with h2 | h2
  · exact x2JColRangeOK_mem _ _ 58 29 c x2JC_2_107_58_29 (by omega) (by omega)
  exact x2JColRangeOK_mem _ _ 87 11 c x2JC_2_107_87_11 (by omega) (by omega)

theorem x2JK_2_108 : x2JKeyOK 2 ⟨108, by decide⟩ = true := by
  apply x2JKeyOK_of_cols
  intro c hc
  have hsz : x2KeySize 2 ⟨108, by decide⟩ = 67 := by decide
  rw [hsz] at hc
  rcases Nat.lt_or_ge c 56 with h0 | h0
  · exact x2JColRangeOK_mem _ _ 0 56 c x2JC_2_108_0_56 (by omega) (by omega)
  exact x2JColRangeOK_mem _ _ 56 11 c x2JC_2_108_56_11 (by omega) (by omega)

theorem x2JK_2_109 : x2JKeyOK 2 ⟨109, by decide⟩ = true := by
  apply x2JKeyOK_of_cols
  intro c hc
  have hsz : x2KeySize 2 ⟨109, by decide⟩ = 57 := by decide
  rw [hsz] at hc
  rcases Nat.lt_or_ge c 46 with h0 | h0
  · exact x2JColRangeOK_mem _ _ 0 46 c x2JC_2_109_0_46 (by omega) (by omega)
  exact x2JColRangeOK_mem _ _ 46 11 c x2JC_2_109_46_11 (by omega) (by omega)

theorem x2JK_2_111 : x2JKeyOK 2 ⟨111, by decide⟩ = true := by
  apply x2JKeyOK_of_cols
  intro c hc
  have hsz : x2KeySize 2 ⟨111, by decide⟩ = 81 := by decide
  rw [hsz] at hc
  rcases Nat.lt_or_ge c 46 with h0 | h0
  · exact x2JColRangeOK_mem _ _ 0 46 c x2JC_2_111_0_46 (by omega) (by omega)
  exact x2JColRangeOK_mem _ _ 46 35 c x2JC_2_111_46_35 (by omega) (by omega)

theorem x2JK_2_112 : x2JKeyOK 2 ⟨112, by decide⟩ = true := by
  apply x2JKeyOK_of_cols
  intro c hc
  have hsz : x2KeySize 2 ⟨112, by decide⟩ = 70 := by decide
  rw [hsz] at hc
  rcases Nat.lt_or_ge c 39 with h0 | h0
  · exact x2JColRangeOK_mem _ _ 0 39 c x2JC_2_112_0_39 (by omega) (by omega)
  exact x2JColRangeOK_mem _ _ 39 31 c x2JC_2_112_39_31 (by omega) (by omega)

theorem x2JKeyOK_all_2 : ∀ k : x2Key 2, x2JKeyOK 2 k = true := by
  intro k
  obtain ⟨kv, hk⟩ := k
  have hk' : kv < 123 := hk
  rcases Nat.lt_or_ge kv 52 with h0 | h0
  · exact x2JKeyRangeOK_mem 2 0 52 x2JR_2_0_52 ⟨kv, hk⟩ (show 0 ≤ kv by omega) (show kv < 0 + 52 by omega)
  rcases Nat.lt_or_ge kv 67 with h1 | h1
  · exact x2JKeyRangeOK_mem 2 52 15 x2JR_2_52_15 ⟨kv, hk⟩ (show 52 ≤ kv by omega) (show kv < 52 + 15 by omega)
  rcases Nat.lt_or_ge kv 76 with h2 | h2
  · exact x2JKeyRangeOK_mem 2 67 9 x2JR_2_67_9 ⟨kv, hk⟩ (show 67 ≤ kv by omega) (show kv < 67 + 9 by omega)
  rcases Nat.lt_or_ge kv 82 with h3 | h3
  · exact x2JKeyRangeOK_mem 2 76 6 x2JR_2_76_6 ⟨kv, hk⟩ (show 76 ≤ kv by omega) (show kv < 76 + 6 by omega)
  rcases Nat.lt_or_ge kv 92 with h4 | h4
  · exact x2JKeyRangeOK_mem 2 82 10 x2JR_2_82_10 ⟨kv, hk⟩ (show 82 ≤ kv by omega) (show kv < 82 + 10 by omega)
  rcases Nat.lt_or_ge kv 93 with h5 | h5
  · exact x2JKeyRangeOK_mem 2 92 1 x2JR_2_92_1 ⟨kv, hk⟩ (show 92 ≤ kv by omega) (show kv < 92 + 1 by omega)
  rcases Nat.lt_or_ge kv 99 with h6 | h6
  · exact x2JKeyRangeOK_mem 2 93 6 x2JR_2_93_6 ⟨kv, hk⟩ (show 93 ≤ kv by omega) (show kv < 93 + 6 by omega)
  rcases Nat.lt_or_ge kv 101 with h7 | h7
  · exact x2JKeyRangeOK_mem 2 99 2 x2JR_2_99_2 ⟨kv, hk⟩ (show 99 ≤ kv by omega) (show kv < 99 + 2 by omega)
  rcases Nat.lt_or_ge kv 102 with h8 | h8
  · obtain rfl : kv = 101 := by omega
    exact x2JK_2_101
  rcases Nat.lt_or_ge kv 103 with h9 | h9
  · obtain rfl : kv = 102 := by omega
    exact x2JK_2_102
  rcases Nat.lt_or_ge kv 104 with h10 | h10
  · exact x2JKeyRangeOK_mem 2 103 1 x2JR_2_103_1 ⟨kv, hk⟩ (show 103 ≤ kv by omega) (show kv < 103 + 1 by omega)
  rcases Nat.lt_or_ge kv 105 with h11 | h11
  · obtain rfl : kv = 104 := by omega
    exact x2JK_2_104
  rcases Nat.lt_or_ge kv 106 with h12 | h12
  · obtain rfl : kv = 105 := by omega
    exact x2JK_2_105
  rcases Nat.lt_or_ge kv 107 with h13 | h13
  · obtain rfl : kv = 106 := by omega
    exact x2JK_2_106
  rcases Nat.lt_or_ge kv 108 with h14 | h14
  · obtain rfl : kv = 107 := by omega
    exact x2JK_2_107
  rcases Nat.lt_or_ge kv 109 with h15 | h15
  · obtain rfl : kv = 108 := by omega
    exact x2JK_2_108
  rcases Nat.lt_or_ge kv 110 with h16 | h16
  · obtain rfl : kv = 109 := by omega
    exact x2JK_2_109
  rcases Nat.lt_or_ge kv 111 with h17 | h17
  · exact x2JKeyRangeOK_mem 2 110 1 x2JR_2_110_1 ⟨kv, hk⟩ (show 110 ≤ kv by omega) (show kv < 110 + 1 by omega)
  rcases Nat.lt_or_ge kv 112 with h18 | h18
  · obtain rfl : kv = 111 := by omega
    exact x2JK_2_111
  rcases Nat.lt_or_ge kv 113 with h19 | h19
  · obtain rfl : kv = 112 := by omega
    exact x2JK_2_112
  rcases Nat.lt_or_ge kv 117 with h20 | h20
  · exact x2JKeyRangeOK_mem 2 113 4 x2JR_2_113_4 ⟨kv, hk⟩ (show 113 ≤ kv by omega) (show kv < 113 + 4 by omega)
  rcases Nat.lt_or_ge kv 118 with h21 | h21
  · exact x2JKeyRangeOK_mem 2 117 1 x2JR_2_117_1 ⟨kv, hk⟩ (show 117 ≤ kv by omega) (show kv < 117 + 1 by omega)
  rcases Nat.lt_or_ge kv 119 with h22 | h22
  · exact x2JKeyRangeOK_mem 2 118 1 x2JR_2_118_1 ⟨kv, hk⟩ (show 118 ≤ kv by omega) (show kv < 118 + 1 by omega)
  rcases Nat.lt_or_ge kv 120 with h23 | h23
  · exact x2JKeyRangeOK_mem 2 119 1 x2JR_2_119_1 ⟨kv, hk⟩ (show 119 ≤ kv by omega) (show kv < 119 + 1 by omega)
  exact x2JKeyRangeOK_mem 2 120 3 x2JR_2_120_3 ⟨kv, hk⟩ (show 120 ≤ kv by omega) (show kv < 120 + 3 by omega)

theorem x2KeyTypes_sorted_2 : ∀ k : x2Key 2, x2Sorted (x2KeyTypes 2 k) := by
  have h : ∀ k : x2Key 2, x2KeyTypes 2 k 0 ≤ x2KeyTypes 2 k 1 ∧ x2KeyTypes 2 k 1 ≤ x2KeyTypes 2 k 2 := by
    decide +kernel
  exact h

/-- Stabilizer invariance of the input blocks of all degree-1 keys of the source sectors 1, 2 (for every
source `N`): the hypothesis `hinv` of `x2FullTensor_sorted` for these keys. -/
theorem x2InputBlock_inv_deg1_concrete (s : Fin 3) (hs : s = 1 ∨ s = 2) (N : X2Blocks s) (k : x2Key s)
    (hdeg : x2KeyDegree s k ≠ 2) (p : Fin 6) (hp : x2KeyTypes s k ∘ x2Perm3 p = x2KeyTypes s k)
    (a b : Fin 3 → ℕ) :
    x2Lookup (x2InputBlock x2DataConcrete s N k) (a ∘ x2Perm3 p) (b ∘ x2Perm3 p) =
      x2Lookup (x2InputBlock x2DataConcrete s N k) a b := by
  rcases hs with rfl | rfl
  · exact x2InputBlock_inv_of_ok 1 N k (x2JKeyOK_all_1 k) hdeg (x2KeyTypes_sorted_1 k) p hp a b
  · exact x2InputBlock_inv_of_ok 2 N k (x2JKeyOK_all_2 k) hdeg (x2KeyTypes_sorted_2 k) p hp a b

end ThreeCopyQutritWerner.X2
