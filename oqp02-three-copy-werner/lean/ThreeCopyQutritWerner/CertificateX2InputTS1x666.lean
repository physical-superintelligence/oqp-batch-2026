module

public import ThreeCopyQutritWerner.CertificateX2InputU1x666x0
public import ThreeCopyQutritWerner.CertificateX2InputU1x666x1
public import ThreeCopyQutritWerner.CertificateX2InputU1x666x2
public import ThreeCopyQutritWerner.CertificateX2InputU1x666x3
public import ThreeCopyQutritWerner.CertificateX2InputU1x666x4
public import ThreeCopyQutritWerner.CertificateX2InputU1x666x5
public import ThreeCopyQutritWerner.CertificateX2InputU1x666x6
public import ThreeCopyQutritWerner.CertificateX2InputU1x666x7
public import ThreeCopyQutritWerner.CertificateX2InputU1x666x8
public import ThreeCopyQutritWerner.CertificateX2InputU1x666x9
public import ThreeCopyQutritWerner.CertificateX2InputU1x666x10
public import ThreeCopyQutritWerner.CertificateX2InputU1x666x11
public import ThreeCopyQutritWerner.CertificateX2InputU1x666x12
public import ThreeCopyQutritWerner.CertificateX2InputU1x666x13
public import ThreeCopyQutritWerner.CertificateX2InputU1x666x14
public import ThreeCopyQutritWerner.CertificateX2InputU1x666x15
public import ThreeCopyQutritWerner.CertificateX2InputU1x666x16

@[expose] public section


/-! S-pipeline T-tables of the type triple (6, 6, 6) of sector 1 and their specification (sigma * x2EmbedS at every label triple). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x666
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

x2_ub_table UBT ub 17 17
x2_tt_gen TT UBT 17 17 17 0

theorem shape : ∀ a0 < x2Mult 1 6, ∀ a1 < x2Mult 1 6, ((UBT.getD a0 []).getD a1 []).length = x2Mult 1 6 ∧ ∀ l ∈ (UBT.getD a0 []).getD a1 [], l.length = x2Mult 1 6 := by
  show ∀ a0 < 17, ∀ a1 < 17, ((UBT.getD a0 []).getD a1 []).length = 17 ∧ ∀ l ∈ (UBT.getD a0 []).getD a1 [], l.length = 17
  intro a0 h0 a1 h1
  interval_cases a0 <;> interval_cases a1
  · exact ubs_0_0
  · exact ubs_0_1
  · exact ubs_0_2
  · exact ubs_0_3
  · exact ubs_0_4
  · exact ubs_0_5
  · exact ubs_0_6
  · exact ubs_0_7
  · exact ubs_0_8
  · exact ubs_0_9
  · exact ubs_0_10
  · exact ubs_0_11
  · exact ubs_0_12
  · exact ubs_0_13
  · exact ubs_0_14
  · exact ubs_0_15
  · exact ubs_0_16
  · exact ubs_1_0
  · exact ubs_1_1
  · exact ubs_1_2
  · exact ubs_1_3
  · exact ubs_1_4
  · exact ubs_1_5
  · exact ubs_1_6
  · exact ubs_1_7
  · exact ubs_1_8
  · exact ubs_1_9
  · exact ubs_1_10
  · exact ubs_1_11
  · exact ubs_1_12
  · exact ubs_1_13
  · exact ubs_1_14
  · exact ubs_1_15
  · exact ubs_1_16
  · exact ubs_2_0
  · exact ubs_2_1
  · exact ubs_2_2
  · exact ubs_2_3
  · exact ubs_2_4
  · exact ubs_2_5
  · exact ubs_2_6
  · exact ubs_2_7
  · exact ubs_2_8
  · exact ubs_2_9
  · exact ubs_2_10
  · exact ubs_2_11
  · exact ubs_2_12
  · exact ubs_2_13
  · exact ubs_2_14
  · exact ubs_2_15
  · exact ubs_2_16
  · exact ubs_3_0
  · exact ubs_3_1
  · exact ubs_3_2
  · exact ubs_3_3
  · exact ubs_3_4
  · exact ubs_3_5
  · exact ubs_3_6
  · exact ubs_3_7
  · exact ubs_3_8
  · exact ubs_3_9
  · exact ubs_3_10
  · exact ubs_3_11
  · exact ubs_3_12
  · exact ubs_3_13
  · exact ubs_3_14
  · exact ubs_3_15
  · exact ubs_3_16
  · exact ubs_4_0
  · exact ubs_4_1
  · exact ubs_4_2
  · exact ubs_4_3
  · exact ubs_4_4
  · exact ubs_4_5
  · exact ubs_4_6
  · exact ubs_4_7
  · exact ubs_4_8
  · exact ubs_4_9
  · exact ubs_4_10
  · exact ubs_4_11
  · exact ubs_4_12
  · exact ubs_4_13
  · exact ubs_4_14
  · exact ubs_4_15
  · exact ubs_4_16
  · exact ubs_5_0
  · exact ubs_5_1
  · exact ubs_5_2
  · exact ubs_5_3
  · exact ubs_5_4
  · exact ubs_5_5
  · exact ubs_5_6
  · exact ubs_5_7
  · exact ubs_5_8
  · exact ubs_5_9
  · exact ubs_5_10
  · exact ubs_5_11
  · exact ubs_5_12
  · exact ubs_5_13
  · exact ubs_5_14
  · exact ubs_5_15
  · exact ubs_5_16
  · exact ubs_6_0
  · exact ubs_6_1
  · exact ubs_6_2
  · exact ubs_6_3
  · exact ubs_6_4
  · exact ubs_6_5
  · exact ubs_6_6
  · exact ubs_6_7
  · exact ubs_6_8
  · exact ubs_6_9
  · exact ubs_6_10
  · exact ubs_6_11
  · exact ubs_6_12
  · exact ubs_6_13
  · exact ubs_6_14
  · exact ubs_6_15
  · exact ubs_6_16
  · exact ubs_7_0
  · exact ubs_7_1
  · exact ubs_7_2
  · exact ubs_7_3
  · exact ubs_7_4
  · exact ubs_7_5
  · exact ubs_7_6
  · exact ubs_7_7
  · exact ubs_7_8
  · exact ubs_7_9
  · exact ubs_7_10
  · exact ubs_7_11
  · exact ubs_7_12
  · exact ubs_7_13
  · exact ubs_7_14
  · exact ubs_7_15
  · exact ubs_7_16
  · exact ubs_8_0
  · exact ubs_8_1
  · exact ubs_8_2
  · exact ubs_8_3
  · exact ubs_8_4
  · exact ubs_8_5
  · exact ubs_8_6
  · exact ubs_8_7
  · exact ubs_8_8
  · exact ubs_8_9
  · exact ubs_8_10
  · exact ubs_8_11
  · exact ubs_8_12
  · exact ubs_8_13
  · exact ubs_8_14
  · exact ubs_8_15
  · exact ubs_8_16
  · exact ubs_9_0
  · exact ubs_9_1
  · exact ubs_9_2
  · exact ubs_9_3
  · exact ubs_9_4
  · exact ubs_9_5
  · exact ubs_9_6
  · exact ubs_9_7
  · exact ubs_9_8
  · exact ubs_9_9
  · exact ubs_9_10
  · exact ubs_9_11
  · exact ubs_9_12
  · exact ubs_9_13
  · exact ubs_9_14
  · exact ubs_9_15
  · exact ubs_9_16
  · exact ubs_10_0
  · exact ubs_10_1
  · exact ubs_10_2
  · exact ubs_10_3
  · exact ubs_10_4
  · exact ubs_10_5
  · exact ubs_10_6
  · exact ubs_10_7
  · exact ubs_10_8
  · exact ubs_10_9
  · exact ubs_10_10
  · exact ubs_10_11
  · exact ubs_10_12
  · exact ubs_10_13
  · exact ubs_10_14
  · exact ubs_10_15
  · exact ubs_10_16
  · exact ubs_11_0
  · exact ubs_11_1
  · exact ubs_11_2
  · exact ubs_11_3
  · exact ubs_11_4
  · exact ubs_11_5
  · exact ubs_11_6
  · exact ubs_11_7
  · exact ubs_11_8
  · exact ubs_11_9
  · exact ubs_11_10
  · exact ubs_11_11
  · exact ubs_11_12
  · exact ubs_11_13
  · exact ubs_11_14
  · exact ubs_11_15
  · exact ubs_11_16
  · exact ubs_12_0
  · exact ubs_12_1
  · exact ubs_12_2
  · exact ubs_12_3
  · exact ubs_12_4
  · exact ubs_12_5
  · exact ubs_12_6
  · exact ubs_12_7
  · exact ubs_12_8
  · exact ubs_12_9
  · exact ubs_12_10
  · exact ubs_12_11
  · exact ubs_12_12
  · exact ubs_12_13
  · exact ubs_12_14
  · exact ubs_12_15
  · exact ubs_12_16
  · exact ubs_13_0
  · exact ubs_13_1
  · exact ubs_13_2
  · exact ubs_13_3
  · exact ubs_13_4
  · exact ubs_13_5
  · exact ubs_13_6
  · exact ubs_13_7
  · exact ubs_13_8
  · exact ubs_13_9
  · exact ubs_13_10
  · exact ubs_13_11
  · exact ubs_13_12
  · exact ubs_13_13
  · exact ubs_13_14
  · exact ubs_13_15
  · exact ubs_13_16
  · exact ubs_14_0
  · exact ubs_14_1
  · exact ubs_14_2
  · exact ubs_14_3
  · exact ubs_14_4
  · exact ubs_14_5
  · exact ubs_14_6
  · exact ubs_14_7
  · exact ubs_14_8
  · exact ubs_14_9
  · exact ubs_14_10
  · exact ubs_14_11
  · exact ubs_14_12
  · exact ubs_14_13
  · exact ubs_14_14
  · exact ubs_14_15
  · exact ubs_14_16
  · exact ubs_15_0
  · exact ubs_15_1
  · exact ubs_15_2
  · exact ubs_15_3
  · exact ubs_15_4
  · exact ubs_15_5
  · exact ubs_15_6
  · exact ubs_15_7
  · exact ubs_15_8
  · exact ubs_15_9
  · exact ubs_15_10
  · exact ubs_15_11
  · exact ubs_15_12
  · exact ubs_15_13
  · exact ubs_15_14
  · exact ubs_15_15
  · exact ubs_15_16
  · exact ubs_16_0
  · exact ubs_16_1
  · exact ubs_16_2
  · exact ubs_16_3
  · exact ubs_16_4
  · exact ubs_16_5
  · exact ubs_16_6
  · exact ubs_16_7
  · exact ubs_16_8
  · exact ubs_16_9
  · exact ubs_16_10
  · exact ubs_16_11
  · exact ubs_16_12
  · exact ubs_16_13
  · exact ubs_16_14
  · exact ubs_16_15
  · exact ubs_16_16
theorem hchk : ubRowsOK (x2Mult 1 6 * x2Mult 1 6 * x2Mult 1 6) (x2Mult 1 6) (x2Mult 1 6) (x2Mult 1 6) (ks.flatMap Prod.snd) UBT := by
  show ∀ a0 < 17, ∀ a1 < 17, ∀ a2 < 17, ∃ lo R : ℕ, lo ≤ a2 ∧ a2 < lo + R ∧ lo + R ≤ 17 ∧ ibBatchOK 256 4913 302 17 289 lo R ((a0 * 17 + a1) * 17 + lo) (ks.flatMap Prod.snd) ((UBT.getD a0 []).getD a1 []).flatten = true
  intro a0 h0 a1 h1 a2 h2
  interval_cases a0 <;> interval_cases a1
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_0_0_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_0_0_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_0_0_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_0_0_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_0_0_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_0_0_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_0_0_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_0_0_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_0_0_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_0_0_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_0_0_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_0_0_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_0_0_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_0_0_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_0_0_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_0_0_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_0_0_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_0_1_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_0_1_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_0_1_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_0_1_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_0_1_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_0_1_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_0_1_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_0_1_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_0_1_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_0_1_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_0_1_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_0_1_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_0_1_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_0_1_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_0_1_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_0_1_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_0_1_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_0_2_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_0_2_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_0_2_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_0_2_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_0_2_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_0_2_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_0_2_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_0_2_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_0_2_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_0_2_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_0_2_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_0_2_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_0_2_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_0_2_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_0_2_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_0_2_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_0_2_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_0_3_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_0_3_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_0_3_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_0_3_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_0_3_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_0_3_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_0_3_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_0_3_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_0_3_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_0_3_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_0_3_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_0_3_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_0_3_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_0_3_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_0_3_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_0_3_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_0_3_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_0_4_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_0_4_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_0_4_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_0_4_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_0_4_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_0_4_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_0_4_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_0_4_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_0_4_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_0_4_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_0_4_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_0_4_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_0_4_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_0_4_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_0_4_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_0_4_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_0_4_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_0_5_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_0_5_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_0_5_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_0_5_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_0_5_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_0_5_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_0_5_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_0_5_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_0_5_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_0_5_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_0_5_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_0_5_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_0_5_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_0_5_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_0_5_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_0_5_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_0_5_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_0_6_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_0_6_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_0_6_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_0_6_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_0_6_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_0_6_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_0_6_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_0_6_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_0_6_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_0_6_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_0_6_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_0_6_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_0_6_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_0_6_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_0_6_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_0_6_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_0_6_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_0_7_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_0_7_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_0_7_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_0_7_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_0_7_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_0_7_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_0_7_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_0_7_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_0_7_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_0_7_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_0_7_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_0_7_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_0_7_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_0_7_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_0_7_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_0_7_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_0_7_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_0_8_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_0_8_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_0_8_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_0_8_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_0_8_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_0_8_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_0_8_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_0_8_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_0_8_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_0_8_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_0_8_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_0_8_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_0_8_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_0_8_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_0_8_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_0_8_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_0_8_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_0_9_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_0_9_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_0_9_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_0_9_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_0_9_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_0_9_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_0_9_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_0_9_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_0_9_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_0_9_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_0_9_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_0_9_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_0_9_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_0_9_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_0_9_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_0_9_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_0_9_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_0_10_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_0_10_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_0_10_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_0_10_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_0_10_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_0_10_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_0_10_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_0_10_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_0_10_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_0_10_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_0_10_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_0_10_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_0_10_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_0_10_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_0_10_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_0_10_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_0_10_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_0_11_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_0_11_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_0_11_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_0_11_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_0_11_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_0_11_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_0_11_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_0_11_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_0_11_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_0_11_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_0_11_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_0_11_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_0_11_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_0_11_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_0_11_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_0_11_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_0_11_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_0_12_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_0_12_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_0_12_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_0_12_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_0_12_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_0_12_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_0_12_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_0_12_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_0_12_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_0_12_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_0_12_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_0_12_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_0_12_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_0_12_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_0_12_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_0_12_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_0_12_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_0_13_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_0_13_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_0_13_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_0_13_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_0_13_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_0_13_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_0_13_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_0_13_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_0_13_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_0_13_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_0_13_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_0_13_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_0_13_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_0_13_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_0_13_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_0_13_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_0_13_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_0_14_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_0_14_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_0_14_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_0_14_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_0_14_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_0_14_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_0_14_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_0_14_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_0_14_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_0_14_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_0_14_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_0_14_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_0_14_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_0_14_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_0_14_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_0_14_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_0_14_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_0_15_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_0_15_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_0_15_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_0_15_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_0_15_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_0_15_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_0_15_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_0_15_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_0_15_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_0_15_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_0_15_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_0_15_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_0_15_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_0_15_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_0_15_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_0_15_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_0_15_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_0_16_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_0_16_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_0_16_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_0_16_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_0_16_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_0_16_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_0_16_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_0_16_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_0_16_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_0_16_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_0_16_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_0_16_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_0_16_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_0_16_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_0_16_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_0_16_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_0_16_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_1_0_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_1_0_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_1_0_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_1_0_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_1_0_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_1_0_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_1_0_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_1_0_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_1_0_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_1_0_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_1_0_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_1_0_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_1_0_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_1_0_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_1_0_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_1_0_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_1_0_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_1_1_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_1_1_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_1_1_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_1_1_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_1_1_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_1_1_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_1_1_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_1_1_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_1_1_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_1_1_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_1_1_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_1_1_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_1_1_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_1_1_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_1_1_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_1_1_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_1_1_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_1_2_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_1_2_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_1_2_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_1_2_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_1_2_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_1_2_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_1_2_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_1_2_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_1_2_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_1_2_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_1_2_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_1_2_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_1_2_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_1_2_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_1_2_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_1_2_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_1_2_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_1_3_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_1_3_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_1_3_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_1_3_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_1_3_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_1_3_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_1_3_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_1_3_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_1_3_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_1_3_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_1_3_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_1_3_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_1_3_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_1_3_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_1_3_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_1_3_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_1_3_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_1_4_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_1_4_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_1_4_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_1_4_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_1_4_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_1_4_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_1_4_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_1_4_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_1_4_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_1_4_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_1_4_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_1_4_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_1_4_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_1_4_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_1_4_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_1_4_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_1_4_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_1_5_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_1_5_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_1_5_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_1_5_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_1_5_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_1_5_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_1_5_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_1_5_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_1_5_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_1_5_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_1_5_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_1_5_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_1_5_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_1_5_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_1_5_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_1_5_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_1_5_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_1_6_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_1_6_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_1_6_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_1_6_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_1_6_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_1_6_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_1_6_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_1_6_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_1_6_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_1_6_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_1_6_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_1_6_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_1_6_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_1_6_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_1_6_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_1_6_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_1_6_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_1_7_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_1_7_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_1_7_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_1_7_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_1_7_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_1_7_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_1_7_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_1_7_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_1_7_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_1_7_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_1_7_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_1_7_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_1_7_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_1_7_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_1_7_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_1_7_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_1_7_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_1_8_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_1_8_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_1_8_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_1_8_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_1_8_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_1_8_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_1_8_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_1_8_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_1_8_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_1_8_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_1_8_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_1_8_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_1_8_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_1_8_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_1_8_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_1_8_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_1_8_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_1_9_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_1_9_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_1_9_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_1_9_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_1_9_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_1_9_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_1_9_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_1_9_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_1_9_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_1_9_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_1_9_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_1_9_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_1_9_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_1_9_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_1_9_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_1_9_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_1_9_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_1_10_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_1_10_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_1_10_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_1_10_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_1_10_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_1_10_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_1_10_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_1_10_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_1_10_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_1_10_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_1_10_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_1_10_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_1_10_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_1_10_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_1_10_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_1_10_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_1_10_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_1_11_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_1_11_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_1_11_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_1_11_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_1_11_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_1_11_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_1_11_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_1_11_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_1_11_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_1_11_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_1_11_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_1_11_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_1_11_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_1_11_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_1_11_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_1_11_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_1_11_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_1_12_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_1_12_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_1_12_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_1_12_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_1_12_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_1_12_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_1_12_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_1_12_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_1_12_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_1_12_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_1_12_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_1_12_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_1_12_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_1_12_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_1_12_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_1_12_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_1_12_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_1_13_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_1_13_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_1_13_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_1_13_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_1_13_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_1_13_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_1_13_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_1_13_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_1_13_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_1_13_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_1_13_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_1_13_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_1_13_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_1_13_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_1_13_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_1_13_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_1_13_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_1_14_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_1_14_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_1_14_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_1_14_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_1_14_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_1_14_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_1_14_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_1_14_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_1_14_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_1_14_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_1_14_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_1_14_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_1_14_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_1_14_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_1_14_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_1_14_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_1_14_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_1_15_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_1_15_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_1_15_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_1_15_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_1_15_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_1_15_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_1_15_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_1_15_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_1_15_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_1_15_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_1_15_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_1_15_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_1_15_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_1_15_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_1_15_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_1_15_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_1_15_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_1_16_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_1_16_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_1_16_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_1_16_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_1_16_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_1_16_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_1_16_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_1_16_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_1_16_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_1_16_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_1_16_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_1_16_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_1_16_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_1_16_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_1_16_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_1_16_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_1_16_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_2_0_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_2_0_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_2_0_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_2_0_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_2_0_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_2_0_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_2_0_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_2_0_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_2_0_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_2_0_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_2_0_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_2_0_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_2_0_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_2_0_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_2_0_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_2_0_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_2_0_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_2_1_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_2_1_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_2_1_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_2_1_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_2_1_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_2_1_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_2_1_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_2_1_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_2_1_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_2_1_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_2_1_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_2_1_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_2_1_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_2_1_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_2_1_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_2_1_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_2_1_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_2_2_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_2_2_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_2_2_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_2_2_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_2_2_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_2_2_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_2_2_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_2_2_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_2_2_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_2_2_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_2_2_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_2_2_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_2_2_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_2_2_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_2_2_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_2_2_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_2_2_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_2_3_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_2_3_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_2_3_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_2_3_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_2_3_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_2_3_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_2_3_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_2_3_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_2_3_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_2_3_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_2_3_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_2_3_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_2_3_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_2_3_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_2_3_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_2_3_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_2_3_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_2_4_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_2_4_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_2_4_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_2_4_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_2_4_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_2_4_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_2_4_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_2_4_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_2_4_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_2_4_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_2_4_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_2_4_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_2_4_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_2_4_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_2_4_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_2_4_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_2_4_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_2_5_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_2_5_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_2_5_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_2_5_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_2_5_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_2_5_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_2_5_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_2_5_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_2_5_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_2_5_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_2_5_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_2_5_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_2_5_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_2_5_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_2_5_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_2_5_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_2_5_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_2_6_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_2_6_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_2_6_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_2_6_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_2_6_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_2_6_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_2_6_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_2_6_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_2_6_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_2_6_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_2_6_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_2_6_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_2_6_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_2_6_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_2_6_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_2_6_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_2_6_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_2_7_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_2_7_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_2_7_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_2_7_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_2_7_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_2_7_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_2_7_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_2_7_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_2_7_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_2_7_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_2_7_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_2_7_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_2_7_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_2_7_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_2_7_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_2_7_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_2_7_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_2_8_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_2_8_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_2_8_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_2_8_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_2_8_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_2_8_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_2_8_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_2_8_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_2_8_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_2_8_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_2_8_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_2_8_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_2_8_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_2_8_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_2_8_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_2_8_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_2_8_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_2_9_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_2_9_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_2_9_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_2_9_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_2_9_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_2_9_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_2_9_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_2_9_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_2_9_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_2_9_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_2_9_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_2_9_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_2_9_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_2_9_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_2_9_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_2_9_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_2_9_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_2_10_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_2_10_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_2_10_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_2_10_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_2_10_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_2_10_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_2_10_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_2_10_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_2_10_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_2_10_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_2_10_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_2_10_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_2_10_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_2_10_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_2_10_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_2_10_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_2_10_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_2_11_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_2_11_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_2_11_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_2_11_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_2_11_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_2_11_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_2_11_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_2_11_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_2_11_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_2_11_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_2_11_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_2_11_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_2_11_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_2_11_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_2_11_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_2_11_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_2_11_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_2_12_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_2_12_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_2_12_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_2_12_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_2_12_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_2_12_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_2_12_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_2_12_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_2_12_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_2_12_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_2_12_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_2_12_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_2_12_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_2_12_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_2_12_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_2_12_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_2_12_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_2_13_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_2_13_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_2_13_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_2_13_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_2_13_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_2_13_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_2_13_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_2_13_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_2_13_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_2_13_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_2_13_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_2_13_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_2_13_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_2_13_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_2_13_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_2_13_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_2_13_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_2_14_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_2_14_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_2_14_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_2_14_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_2_14_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_2_14_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_2_14_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_2_14_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_2_14_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_2_14_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_2_14_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_2_14_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_2_14_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_2_14_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_2_14_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_2_14_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_2_14_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_2_15_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_2_15_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_2_15_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_2_15_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_2_15_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_2_15_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_2_15_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_2_15_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_2_15_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_2_15_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_2_15_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_2_15_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_2_15_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_2_15_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_2_15_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_2_15_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_2_15_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_2_16_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_2_16_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_2_16_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_2_16_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_2_16_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_2_16_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_2_16_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_2_16_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_2_16_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_2_16_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_2_16_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_2_16_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_2_16_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_2_16_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_2_16_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_2_16_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_2_16_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_3_0_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_3_0_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_3_0_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_3_0_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_3_0_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_3_0_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_3_0_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_3_0_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_3_0_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_3_0_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_3_0_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_3_0_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_3_0_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_3_0_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_3_0_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_3_0_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_3_0_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_3_1_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_3_1_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_3_1_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_3_1_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_3_1_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_3_1_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_3_1_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_3_1_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_3_1_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_3_1_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_3_1_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_3_1_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_3_1_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_3_1_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_3_1_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_3_1_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_3_1_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_3_2_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_3_2_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_3_2_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_3_2_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_3_2_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_3_2_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_3_2_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_3_2_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_3_2_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_3_2_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_3_2_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_3_2_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_3_2_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_3_2_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_3_2_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_3_2_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_3_2_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_3_3_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_3_3_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_3_3_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_3_3_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_3_3_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_3_3_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_3_3_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_3_3_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_3_3_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_3_3_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_3_3_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_3_3_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_3_3_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_3_3_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_3_3_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_3_3_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_3_3_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_3_4_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_3_4_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_3_4_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_3_4_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_3_4_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_3_4_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_3_4_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_3_4_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_3_4_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_3_4_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_3_4_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_3_4_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_3_4_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_3_4_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_3_4_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_3_4_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_3_4_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_3_5_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_3_5_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_3_5_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_3_5_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_3_5_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_3_5_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_3_5_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_3_5_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_3_5_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_3_5_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_3_5_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_3_5_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_3_5_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_3_5_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_3_5_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_3_5_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_3_5_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_3_6_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_3_6_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_3_6_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_3_6_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_3_6_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_3_6_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_3_6_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_3_6_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_3_6_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_3_6_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_3_6_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_3_6_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_3_6_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_3_6_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_3_6_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_3_6_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_3_6_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_3_7_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_3_7_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_3_7_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_3_7_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_3_7_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_3_7_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_3_7_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_3_7_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_3_7_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_3_7_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_3_7_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_3_7_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_3_7_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_3_7_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_3_7_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_3_7_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_3_7_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_3_8_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_3_8_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_3_8_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_3_8_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_3_8_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_3_8_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_3_8_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_3_8_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_3_8_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_3_8_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_3_8_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_3_8_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_3_8_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_3_8_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_3_8_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_3_8_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_3_8_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_3_9_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_3_9_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_3_9_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_3_9_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_3_9_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_3_9_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_3_9_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_3_9_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_3_9_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_3_9_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_3_9_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_3_9_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_3_9_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_3_9_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_3_9_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_3_9_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_3_9_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_3_10_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_3_10_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_3_10_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_3_10_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_3_10_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_3_10_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_3_10_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_3_10_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_3_10_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_3_10_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_3_10_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_3_10_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_3_10_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_3_10_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_3_10_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_3_10_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_3_10_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_3_11_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_3_11_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_3_11_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_3_11_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_3_11_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_3_11_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_3_11_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_3_11_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_3_11_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_3_11_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_3_11_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_3_11_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_3_11_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_3_11_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_3_11_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_3_11_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_3_11_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_3_12_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_3_12_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_3_12_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_3_12_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_3_12_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_3_12_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_3_12_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_3_12_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_3_12_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_3_12_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_3_12_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_3_12_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_3_12_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_3_12_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_3_12_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_3_12_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_3_12_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_3_13_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_3_13_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_3_13_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_3_13_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_3_13_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_3_13_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_3_13_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_3_13_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_3_13_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_3_13_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_3_13_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_3_13_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_3_13_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_3_13_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_3_13_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_3_13_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_3_13_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_3_14_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_3_14_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_3_14_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_3_14_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_3_14_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_3_14_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_3_14_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_3_14_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_3_14_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_3_14_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_3_14_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_3_14_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_3_14_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_3_14_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_3_14_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_3_14_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_3_14_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_3_15_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_3_15_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_3_15_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_3_15_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_3_15_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_3_15_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_3_15_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_3_15_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_3_15_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_3_15_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_3_15_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_3_15_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_3_15_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_3_15_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_3_15_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_3_15_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_3_15_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_3_16_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_3_16_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_3_16_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_3_16_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_3_16_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_3_16_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_3_16_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_3_16_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_3_16_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_3_16_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_3_16_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_3_16_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_3_16_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_3_16_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_3_16_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_3_16_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_3_16_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_4_0_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_4_0_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_4_0_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_4_0_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_4_0_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_4_0_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_4_0_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_4_0_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_4_0_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_4_0_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_4_0_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_4_0_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_4_0_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_4_0_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_4_0_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_4_0_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_4_0_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_4_1_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_4_1_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_4_1_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_4_1_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_4_1_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_4_1_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_4_1_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_4_1_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_4_1_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_4_1_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_4_1_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_4_1_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_4_1_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_4_1_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_4_1_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_4_1_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_4_1_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_4_2_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_4_2_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_4_2_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_4_2_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_4_2_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_4_2_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_4_2_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_4_2_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_4_2_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_4_2_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_4_2_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_4_2_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_4_2_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_4_2_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_4_2_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_4_2_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_4_2_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_4_3_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_4_3_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_4_3_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_4_3_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_4_3_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_4_3_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_4_3_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_4_3_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_4_3_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_4_3_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_4_3_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_4_3_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_4_3_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_4_3_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_4_3_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_4_3_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_4_3_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_4_4_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_4_4_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_4_4_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_4_4_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_4_4_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_4_4_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_4_4_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_4_4_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_4_4_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_4_4_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_4_4_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_4_4_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_4_4_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_4_4_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_4_4_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_4_4_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_4_4_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_4_5_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_4_5_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_4_5_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_4_5_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_4_5_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_4_5_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_4_5_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_4_5_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_4_5_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_4_5_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_4_5_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_4_5_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_4_5_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_4_5_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_4_5_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_4_5_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_4_5_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_4_6_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_4_6_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_4_6_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_4_6_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_4_6_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_4_6_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_4_6_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_4_6_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_4_6_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_4_6_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_4_6_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_4_6_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_4_6_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_4_6_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_4_6_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_4_6_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_4_6_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_4_7_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_4_7_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_4_7_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_4_7_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_4_7_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_4_7_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_4_7_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_4_7_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_4_7_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_4_7_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_4_7_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_4_7_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_4_7_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_4_7_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_4_7_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_4_7_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_4_7_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_4_8_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_4_8_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_4_8_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_4_8_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_4_8_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_4_8_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_4_8_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_4_8_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_4_8_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_4_8_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_4_8_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_4_8_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_4_8_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_4_8_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_4_8_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_4_8_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_4_8_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_4_9_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_4_9_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_4_9_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_4_9_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_4_9_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_4_9_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_4_9_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_4_9_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_4_9_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_4_9_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_4_9_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_4_9_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_4_9_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_4_9_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_4_9_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_4_9_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_4_9_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_4_10_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_4_10_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_4_10_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_4_10_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_4_10_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_4_10_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_4_10_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_4_10_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_4_10_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_4_10_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_4_10_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_4_10_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_4_10_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_4_10_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_4_10_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_4_10_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_4_10_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_4_11_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_4_11_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_4_11_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_4_11_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_4_11_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_4_11_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_4_11_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_4_11_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_4_11_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_4_11_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_4_11_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_4_11_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_4_11_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_4_11_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_4_11_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_4_11_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_4_11_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_4_12_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_4_12_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_4_12_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_4_12_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_4_12_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_4_12_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_4_12_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_4_12_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_4_12_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_4_12_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_4_12_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_4_12_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_4_12_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_4_12_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_4_12_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_4_12_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_4_12_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_4_13_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_4_13_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_4_13_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_4_13_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_4_13_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_4_13_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_4_13_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_4_13_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_4_13_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_4_13_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_4_13_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_4_13_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_4_13_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_4_13_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_4_13_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_4_13_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_4_13_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_4_14_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_4_14_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_4_14_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_4_14_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_4_14_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_4_14_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_4_14_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_4_14_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_4_14_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_4_14_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_4_14_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_4_14_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_4_14_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_4_14_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_4_14_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_4_14_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_4_14_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_4_15_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_4_15_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_4_15_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_4_15_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_4_15_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_4_15_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_4_15_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_4_15_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_4_15_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_4_15_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_4_15_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_4_15_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_4_15_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_4_15_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_4_15_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_4_15_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_4_15_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_4_16_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_4_16_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_4_16_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_4_16_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_4_16_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_4_16_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_4_16_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_4_16_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_4_16_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_4_16_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_4_16_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_4_16_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_4_16_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_4_16_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_4_16_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_4_16_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_4_16_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_5_0_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_5_0_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_5_0_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_5_0_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_5_0_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_5_0_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_5_0_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_5_0_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_5_0_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_5_0_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_5_0_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_5_0_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_5_0_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_5_0_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_5_0_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_5_0_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_5_0_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_5_1_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_5_1_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_5_1_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_5_1_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_5_1_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_5_1_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_5_1_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_5_1_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_5_1_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_5_1_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_5_1_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_5_1_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_5_1_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_5_1_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_5_1_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_5_1_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_5_1_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_5_2_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_5_2_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_5_2_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_5_2_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_5_2_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_5_2_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_5_2_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_5_2_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_5_2_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_5_2_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_5_2_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_5_2_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_5_2_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_5_2_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_5_2_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_5_2_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_5_2_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_5_3_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_5_3_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_5_3_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_5_3_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_5_3_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_5_3_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_5_3_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_5_3_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_5_3_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_5_3_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_5_3_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_5_3_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_5_3_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_5_3_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_5_3_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_5_3_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_5_3_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_5_4_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_5_4_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_5_4_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_5_4_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_5_4_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_5_4_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_5_4_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_5_4_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_5_4_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_5_4_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_5_4_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_5_4_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_5_4_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_5_4_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_5_4_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_5_4_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_5_4_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_5_5_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_5_5_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_5_5_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_5_5_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_5_5_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_5_5_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_5_5_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_5_5_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_5_5_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_5_5_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_5_5_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_5_5_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_5_5_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_5_5_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_5_5_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_5_5_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_5_5_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_5_6_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_5_6_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_5_6_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_5_6_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_5_6_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_5_6_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_5_6_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_5_6_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_5_6_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_5_6_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_5_6_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_5_6_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_5_6_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_5_6_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_5_6_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_5_6_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_5_6_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_5_7_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_5_7_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_5_7_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_5_7_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_5_7_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_5_7_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_5_7_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_5_7_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_5_7_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_5_7_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_5_7_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_5_7_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_5_7_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_5_7_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_5_7_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_5_7_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_5_7_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_5_8_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_5_8_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_5_8_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_5_8_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_5_8_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_5_8_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_5_8_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_5_8_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_5_8_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_5_8_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_5_8_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_5_8_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_5_8_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_5_8_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_5_8_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_5_8_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_5_8_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_5_9_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_5_9_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_5_9_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_5_9_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_5_9_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_5_9_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_5_9_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_5_9_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_5_9_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_5_9_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_5_9_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_5_9_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_5_9_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_5_9_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_5_9_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_5_9_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_5_9_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_5_10_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_5_10_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_5_10_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_5_10_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_5_10_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_5_10_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_5_10_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_5_10_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_5_10_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_5_10_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_5_10_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_5_10_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_5_10_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_5_10_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_5_10_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_5_10_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_5_10_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_5_11_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_5_11_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_5_11_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_5_11_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_5_11_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_5_11_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_5_11_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_5_11_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_5_11_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_5_11_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_5_11_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_5_11_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_5_11_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_5_11_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_5_11_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_5_11_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_5_11_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_5_12_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_5_12_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_5_12_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_5_12_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_5_12_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_5_12_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_5_12_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_5_12_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_5_12_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_5_12_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_5_12_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_5_12_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_5_12_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_5_12_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_5_12_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_5_12_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_5_12_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_5_13_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_5_13_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_5_13_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_5_13_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_5_13_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_5_13_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_5_13_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_5_13_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_5_13_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_5_13_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_5_13_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_5_13_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_5_13_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_5_13_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_5_13_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_5_13_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_5_13_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_5_14_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_5_14_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_5_14_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_5_14_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_5_14_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_5_14_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_5_14_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_5_14_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_5_14_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_5_14_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_5_14_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_5_14_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_5_14_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_5_14_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_5_14_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_5_14_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_5_14_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_5_15_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_5_15_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_5_15_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_5_15_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_5_15_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_5_15_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_5_15_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_5_15_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_5_15_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_5_15_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_5_15_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_5_15_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_5_15_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_5_15_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_5_15_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_5_15_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_5_15_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_5_16_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_5_16_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_5_16_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_5_16_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_5_16_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_5_16_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_5_16_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_5_16_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_5_16_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_5_16_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_5_16_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_5_16_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_5_16_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_5_16_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_5_16_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_5_16_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_5_16_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_6_0_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_6_0_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_6_0_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_6_0_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_6_0_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_6_0_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_6_0_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_6_0_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_6_0_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_6_0_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_6_0_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_6_0_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_6_0_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_6_0_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_6_0_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_6_0_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_6_0_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_6_1_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_6_1_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_6_1_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_6_1_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_6_1_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_6_1_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_6_1_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_6_1_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_6_1_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_6_1_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_6_1_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_6_1_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_6_1_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_6_1_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_6_1_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_6_1_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_6_1_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_6_2_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_6_2_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_6_2_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_6_2_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_6_2_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_6_2_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_6_2_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_6_2_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_6_2_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_6_2_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_6_2_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_6_2_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_6_2_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_6_2_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_6_2_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_6_2_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_6_2_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_6_3_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_6_3_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_6_3_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_6_3_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_6_3_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_6_3_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_6_3_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_6_3_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_6_3_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_6_3_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_6_3_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_6_3_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_6_3_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_6_3_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_6_3_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_6_3_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_6_3_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_6_4_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_6_4_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_6_4_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_6_4_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_6_4_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_6_4_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_6_4_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_6_4_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_6_4_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_6_4_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_6_4_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_6_4_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_6_4_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_6_4_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_6_4_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_6_4_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_6_4_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_6_5_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_6_5_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_6_5_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_6_5_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_6_5_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_6_5_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_6_5_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_6_5_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_6_5_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_6_5_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_6_5_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_6_5_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_6_5_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_6_5_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_6_5_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_6_5_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_6_5_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_6_6_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_6_6_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_6_6_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_6_6_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_6_6_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_6_6_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_6_6_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_6_6_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_6_6_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_6_6_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_6_6_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_6_6_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_6_6_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_6_6_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_6_6_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_6_6_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_6_6_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_6_7_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_6_7_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_6_7_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_6_7_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_6_7_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_6_7_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_6_7_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_6_7_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_6_7_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_6_7_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_6_7_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_6_7_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_6_7_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_6_7_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_6_7_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_6_7_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_6_7_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_6_8_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_6_8_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_6_8_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_6_8_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_6_8_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_6_8_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_6_8_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_6_8_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_6_8_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_6_8_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_6_8_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_6_8_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_6_8_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_6_8_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_6_8_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_6_8_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_6_8_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_6_9_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_6_9_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_6_9_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_6_9_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_6_9_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_6_9_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_6_9_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_6_9_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_6_9_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_6_9_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_6_9_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_6_9_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_6_9_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_6_9_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_6_9_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_6_9_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_6_9_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_6_10_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_6_10_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_6_10_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_6_10_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_6_10_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_6_10_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_6_10_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_6_10_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_6_10_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_6_10_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_6_10_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_6_10_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_6_10_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_6_10_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_6_10_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_6_10_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_6_10_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_6_11_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_6_11_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_6_11_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_6_11_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_6_11_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_6_11_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_6_11_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_6_11_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_6_11_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_6_11_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_6_11_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_6_11_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_6_11_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_6_11_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_6_11_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_6_11_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_6_11_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_6_12_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_6_12_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_6_12_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_6_12_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_6_12_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_6_12_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_6_12_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_6_12_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_6_12_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_6_12_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_6_12_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_6_12_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_6_12_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_6_12_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_6_12_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_6_12_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_6_12_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_6_13_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_6_13_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_6_13_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_6_13_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_6_13_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_6_13_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_6_13_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_6_13_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_6_13_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_6_13_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_6_13_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_6_13_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_6_13_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_6_13_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_6_13_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_6_13_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_6_13_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_6_14_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_6_14_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_6_14_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_6_14_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_6_14_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_6_14_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_6_14_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_6_14_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_6_14_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_6_14_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_6_14_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_6_14_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_6_14_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_6_14_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_6_14_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_6_14_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_6_14_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_6_15_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_6_15_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_6_15_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_6_15_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_6_15_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_6_15_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_6_15_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_6_15_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_6_15_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_6_15_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_6_15_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_6_15_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_6_15_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_6_15_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_6_15_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_6_15_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_6_15_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_6_16_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_6_16_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_6_16_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_6_16_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_6_16_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_6_16_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_6_16_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_6_16_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_6_16_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_6_16_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_6_16_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_6_16_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_6_16_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_6_16_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_6_16_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_6_16_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_6_16_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_7_0_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_7_0_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_7_0_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_7_0_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_7_0_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_7_0_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_7_0_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_7_0_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_7_0_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_7_0_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_7_0_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_7_0_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_7_0_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_7_0_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_7_0_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_7_0_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_7_0_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_7_1_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_7_1_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_7_1_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_7_1_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_7_1_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_7_1_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_7_1_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_7_1_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_7_1_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_7_1_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_7_1_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_7_1_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_7_1_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_7_1_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_7_1_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_7_1_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_7_1_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_7_2_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_7_2_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_7_2_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_7_2_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_7_2_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_7_2_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_7_2_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_7_2_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_7_2_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_7_2_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_7_2_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_7_2_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_7_2_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_7_2_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_7_2_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_7_2_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_7_2_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_7_3_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_7_3_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_7_3_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_7_3_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_7_3_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_7_3_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_7_3_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_7_3_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_7_3_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_7_3_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_7_3_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_7_3_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_7_3_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_7_3_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_7_3_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_7_3_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_7_3_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_7_4_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_7_4_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_7_4_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_7_4_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_7_4_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_7_4_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_7_4_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_7_4_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_7_4_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_7_4_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_7_4_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_7_4_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_7_4_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_7_4_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_7_4_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_7_4_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_7_4_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_7_5_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_7_5_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_7_5_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_7_5_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_7_5_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_7_5_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_7_5_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_7_5_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_7_5_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_7_5_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_7_5_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_7_5_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_7_5_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_7_5_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_7_5_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_7_5_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_7_5_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_7_6_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_7_6_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_7_6_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_7_6_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_7_6_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_7_6_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_7_6_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_7_6_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_7_6_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_7_6_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_7_6_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_7_6_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_7_6_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_7_6_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_7_6_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_7_6_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_7_6_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_7_7_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_7_7_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_7_7_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_7_7_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_7_7_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_7_7_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_7_7_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_7_7_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_7_7_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_7_7_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_7_7_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_7_7_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_7_7_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_7_7_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_7_7_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_7_7_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_7_7_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_7_8_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_7_8_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_7_8_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_7_8_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_7_8_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_7_8_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_7_8_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_7_8_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_7_8_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_7_8_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_7_8_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_7_8_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_7_8_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_7_8_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_7_8_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_7_8_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_7_8_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_7_9_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_7_9_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_7_9_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_7_9_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_7_9_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_7_9_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_7_9_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_7_9_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_7_9_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_7_9_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_7_9_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_7_9_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_7_9_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_7_9_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_7_9_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_7_9_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_7_9_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_7_10_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_7_10_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_7_10_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_7_10_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_7_10_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_7_10_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_7_10_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_7_10_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_7_10_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_7_10_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_7_10_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_7_10_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_7_10_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_7_10_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_7_10_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_7_10_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_7_10_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_7_11_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_7_11_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_7_11_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_7_11_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_7_11_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_7_11_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_7_11_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_7_11_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_7_11_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_7_11_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_7_11_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_7_11_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_7_11_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_7_11_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_7_11_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_7_11_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_7_11_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_7_12_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_7_12_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_7_12_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_7_12_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_7_12_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_7_12_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_7_12_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_7_12_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_7_12_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_7_12_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_7_12_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_7_12_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_7_12_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_7_12_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_7_12_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_7_12_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_7_12_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_7_13_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_7_13_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_7_13_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_7_13_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_7_13_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_7_13_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_7_13_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_7_13_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_7_13_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_7_13_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_7_13_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_7_13_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_7_13_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_7_13_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_7_13_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_7_13_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_7_13_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_7_14_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_7_14_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_7_14_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_7_14_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_7_14_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_7_14_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_7_14_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_7_14_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_7_14_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_7_14_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_7_14_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_7_14_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_7_14_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_7_14_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_7_14_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_7_14_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_7_14_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_7_15_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_7_15_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_7_15_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_7_15_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_7_15_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_7_15_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_7_15_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_7_15_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_7_15_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_7_15_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_7_15_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_7_15_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_7_15_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_7_15_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_7_15_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_7_15_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_7_15_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_7_16_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_7_16_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_7_16_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_7_16_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_7_16_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_7_16_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_7_16_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_7_16_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_7_16_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_7_16_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_7_16_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_7_16_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_7_16_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_7_16_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_7_16_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_7_16_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_7_16_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_8_0_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_8_0_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_8_0_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_8_0_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_8_0_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_8_0_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_8_0_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_8_0_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_8_0_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_8_0_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_8_0_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_8_0_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_8_0_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_8_0_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_8_0_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_8_0_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_8_0_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_8_1_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_8_1_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_8_1_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_8_1_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_8_1_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_8_1_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_8_1_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_8_1_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_8_1_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_8_1_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_8_1_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_8_1_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_8_1_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_8_1_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_8_1_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_8_1_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_8_1_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_8_2_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_8_2_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_8_2_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_8_2_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_8_2_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_8_2_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_8_2_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_8_2_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_8_2_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_8_2_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_8_2_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_8_2_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_8_2_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_8_2_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_8_2_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_8_2_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_8_2_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_8_3_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_8_3_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_8_3_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_8_3_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_8_3_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_8_3_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_8_3_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_8_3_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_8_3_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_8_3_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_8_3_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_8_3_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_8_3_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_8_3_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_8_3_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_8_3_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_8_3_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_8_4_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_8_4_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_8_4_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_8_4_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_8_4_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_8_4_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_8_4_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_8_4_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_8_4_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_8_4_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_8_4_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_8_4_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_8_4_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_8_4_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_8_4_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_8_4_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_8_4_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_8_5_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_8_5_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_8_5_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_8_5_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_8_5_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_8_5_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_8_5_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_8_5_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_8_5_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_8_5_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_8_5_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_8_5_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_8_5_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_8_5_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_8_5_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_8_5_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_8_5_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_8_6_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_8_6_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_8_6_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_8_6_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_8_6_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_8_6_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_8_6_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_8_6_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_8_6_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_8_6_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_8_6_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_8_6_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_8_6_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_8_6_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_8_6_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_8_6_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_8_6_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_8_7_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_8_7_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_8_7_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_8_7_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_8_7_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_8_7_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_8_7_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_8_7_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_8_7_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_8_7_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_8_7_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_8_7_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_8_7_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_8_7_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_8_7_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_8_7_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_8_7_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_8_8_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_8_8_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_8_8_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_8_8_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_8_8_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_8_8_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_8_8_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_8_8_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_8_8_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_8_8_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_8_8_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_8_8_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_8_8_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_8_8_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_8_8_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_8_8_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_8_8_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_8_9_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_8_9_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_8_9_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_8_9_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_8_9_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_8_9_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_8_9_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_8_9_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_8_9_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_8_9_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_8_9_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_8_9_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_8_9_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_8_9_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_8_9_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_8_9_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_8_9_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_8_10_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_8_10_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_8_10_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_8_10_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_8_10_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_8_10_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_8_10_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_8_10_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_8_10_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_8_10_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_8_10_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_8_10_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_8_10_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_8_10_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_8_10_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_8_10_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_8_10_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_8_11_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_8_11_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_8_11_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_8_11_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_8_11_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_8_11_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_8_11_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_8_11_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_8_11_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_8_11_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_8_11_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_8_11_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_8_11_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_8_11_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_8_11_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_8_11_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_8_11_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_8_12_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_8_12_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_8_12_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_8_12_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_8_12_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_8_12_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_8_12_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_8_12_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_8_12_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_8_12_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_8_12_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_8_12_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_8_12_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_8_12_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_8_12_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_8_12_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_8_12_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_8_13_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_8_13_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_8_13_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_8_13_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_8_13_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_8_13_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_8_13_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_8_13_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_8_13_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_8_13_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_8_13_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_8_13_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_8_13_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_8_13_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_8_13_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_8_13_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_8_13_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_8_14_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_8_14_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_8_14_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_8_14_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_8_14_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_8_14_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_8_14_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_8_14_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_8_14_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_8_14_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_8_14_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_8_14_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_8_14_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_8_14_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_8_14_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_8_14_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_8_14_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_8_15_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_8_15_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_8_15_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_8_15_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_8_15_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_8_15_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_8_15_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_8_15_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_8_15_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_8_15_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_8_15_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_8_15_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_8_15_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_8_15_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_8_15_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_8_15_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_8_15_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_8_16_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_8_16_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_8_16_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_8_16_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_8_16_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_8_16_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_8_16_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_8_16_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_8_16_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_8_16_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_8_16_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_8_16_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_8_16_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_8_16_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_8_16_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_8_16_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_8_16_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_9_0_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_9_0_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_9_0_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_9_0_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_9_0_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_9_0_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_9_0_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_9_0_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_9_0_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_9_0_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_9_0_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_9_0_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_9_0_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_9_0_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_9_0_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_9_0_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_9_0_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_9_1_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_9_1_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_9_1_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_9_1_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_9_1_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_9_1_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_9_1_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_9_1_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_9_1_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_9_1_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_9_1_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_9_1_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_9_1_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_9_1_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_9_1_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_9_1_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_9_1_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_9_2_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_9_2_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_9_2_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_9_2_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_9_2_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_9_2_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_9_2_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_9_2_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_9_2_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_9_2_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_9_2_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_9_2_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_9_2_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_9_2_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_9_2_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_9_2_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_9_2_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_9_3_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_9_3_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_9_3_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_9_3_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_9_3_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_9_3_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_9_3_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_9_3_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_9_3_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_9_3_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_9_3_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_9_3_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_9_3_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_9_3_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_9_3_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_9_3_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_9_3_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_9_4_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_9_4_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_9_4_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_9_4_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_9_4_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_9_4_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_9_4_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_9_4_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_9_4_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_9_4_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_9_4_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_9_4_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_9_4_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_9_4_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_9_4_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_9_4_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_9_4_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_9_5_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_9_5_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_9_5_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_9_5_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_9_5_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_9_5_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_9_5_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_9_5_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_9_5_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_9_5_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_9_5_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_9_5_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_9_5_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_9_5_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_9_5_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_9_5_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_9_5_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_9_6_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_9_6_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_9_6_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_9_6_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_9_6_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_9_6_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_9_6_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_9_6_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_9_6_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_9_6_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_9_6_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_9_6_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_9_6_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_9_6_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_9_6_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_9_6_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_9_6_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_9_7_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_9_7_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_9_7_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_9_7_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_9_7_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_9_7_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_9_7_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_9_7_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_9_7_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_9_7_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_9_7_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_9_7_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_9_7_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_9_7_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_9_7_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_9_7_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_9_7_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_9_8_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_9_8_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_9_8_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_9_8_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_9_8_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_9_8_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_9_8_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_9_8_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_9_8_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_9_8_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_9_8_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_9_8_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_9_8_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_9_8_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_9_8_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_9_8_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_9_8_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_9_9_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_9_9_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_9_9_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_9_9_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_9_9_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_9_9_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_9_9_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_9_9_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_9_9_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_9_9_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_9_9_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_9_9_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_9_9_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_9_9_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_9_9_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_9_9_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_9_9_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_9_10_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_9_10_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_9_10_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_9_10_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_9_10_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_9_10_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_9_10_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_9_10_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_9_10_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_9_10_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_9_10_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_9_10_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_9_10_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_9_10_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_9_10_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_9_10_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_9_10_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_9_11_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_9_11_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_9_11_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_9_11_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_9_11_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_9_11_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_9_11_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_9_11_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_9_11_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_9_11_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_9_11_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_9_11_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_9_11_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_9_11_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_9_11_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_9_11_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_9_11_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_9_12_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_9_12_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_9_12_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_9_12_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_9_12_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_9_12_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_9_12_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_9_12_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_9_12_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_9_12_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_9_12_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_9_12_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_9_12_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_9_12_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_9_12_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_9_12_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_9_12_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_9_13_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_9_13_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_9_13_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_9_13_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_9_13_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_9_13_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_9_13_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_9_13_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_9_13_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_9_13_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_9_13_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_9_13_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_9_13_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_9_13_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_9_13_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_9_13_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_9_13_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_9_14_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_9_14_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_9_14_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_9_14_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_9_14_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_9_14_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_9_14_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_9_14_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_9_14_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_9_14_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_9_14_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_9_14_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_9_14_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_9_14_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_9_14_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_9_14_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_9_14_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_9_15_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_9_15_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_9_15_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_9_15_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_9_15_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_9_15_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_9_15_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_9_15_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_9_15_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_9_15_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_9_15_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_9_15_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_9_15_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_9_15_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_9_15_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_9_15_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_9_15_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_9_16_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_9_16_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_9_16_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_9_16_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_9_16_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_9_16_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_9_16_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_9_16_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_9_16_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_9_16_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_9_16_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_9_16_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_9_16_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_9_16_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_9_16_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_9_16_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_9_16_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_10_0_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_10_0_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_10_0_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_10_0_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_10_0_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_10_0_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_10_0_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_10_0_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_10_0_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_10_0_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_10_0_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_10_0_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_10_0_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_10_0_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_10_0_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_10_0_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_10_0_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_10_1_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_10_1_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_10_1_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_10_1_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_10_1_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_10_1_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_10_1_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_10_1_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_10_1_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_10_1_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_10_1_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_10_1_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_10_1_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_10_1_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_10_1_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_10_1_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_10_1_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_10_2_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_10_2_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_10_2_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_10_2_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_10_2_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_10_2_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_10_2_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_10_2_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_10_2_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_10_2_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_10_2_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_10_2_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_10_2_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_10_2_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_10_2_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_10_2_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_10_2_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_10_3_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_10_3_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_10_3_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_10_3_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_10_3_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_10_3_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_10_3_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_10_3_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_10_3_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_10_3_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_10_3_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_10_3_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_10_3_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_10_3_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_10_3_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_10_3_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_10_3_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_10_4_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_10_4_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_10_4_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_10_4_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_10_4_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_10_4_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_10_4_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_10_4_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_10_4_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_10_4_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_10_4_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_10_4_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_10_4_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_10_4_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_10_4_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_10_4_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_10_4_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_10_5_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_10_5_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_10_5_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_10_5_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_10_5_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_10_5_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_10_5_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_10_5_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_10_5_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_10_5_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_10_5_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_10_5_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_10_5_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_10_5_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_10_5_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_10_5_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_10_5_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_10_6_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_10_6_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_10_6_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_10_6_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_10_6_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_10_6_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_10_6_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_10_6_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_10_6_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_10_6_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_10_6_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_10_6_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_10_6_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_10_6_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_10_6_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_10_6_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_10_6_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_10_7_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_10_7_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_10_7_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_10_7_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_10_7_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_10_7_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_10_7_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_10_7_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_10_7_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_10_7_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_10_7_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_10_7_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_10_7_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_10_7_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_10_7_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_10_7_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_10_7_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_10_8_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_10_8_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_10_8_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_10_8_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_10_8_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_10_8_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_10_8_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_10_8_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_10_8_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_10_8_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_10_8_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_10_8_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_10_8_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_10_8_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_10_8_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_10_8_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_10_8_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_10_9_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_10_9_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_10_9_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_10_9_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_10_9_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_10_9_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_10_9_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_10_9_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_10_9_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_10_9_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_10_9_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_10_9_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_10_9_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_10_9_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_10_9_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_10_9_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_10_9_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_10_10_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_10_10_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_10_10_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_10_10_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_10_10_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_10_10_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_10_10_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_10_10_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_10_10_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_10_10_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_10_10_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_10_10_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_10_10_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_10_10_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_10_10_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_10_10_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_10_10_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_10_11_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_10_11_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_10_11_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_10_11_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_10_11_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_10_11_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_10_11_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_10_11_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_10_11_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_10_11_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_10_11_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_10_11_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_10_11_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_10_11_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_10_11_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_10_11_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_10_11_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_10_12_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_10_12_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_10_12_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_10_12_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_10_12_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_10_12_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_10_12_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_10_12_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_10_12_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_10_12_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_10_12_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_10_12_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_10_12_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_10_12_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_10_12_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_10_12_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_10_12_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_10_13_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_10_13_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_10_13_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_10_13_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_10_13_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_10_13_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_10_13_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_10_13_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_10_13_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_10_13_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_10_13_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_10_13_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_10_13_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_10_13_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_10_13_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_10_13_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_10_13_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_10_14_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_10_14_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_10_14_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_10_14_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_10_14_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_10_14_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_10_14_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_10_14_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_10_14_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_10_14_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_10_14_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_10_14_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_10_14_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_10_14_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_10_14_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_10_14_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_10_14_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_10_15_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_10_15_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_10_15_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_10_15_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_10_15_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_10_15_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_10_15_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_10_15_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_10_15_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_10_15_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_10_15_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_10_15_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_10_15_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_10_15_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_10_15_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_10_15_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_10_15_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_10_16_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_10_16_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_10_16_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_10_16_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_10_16_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_10_16_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_10_16_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_10_16_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_10_16_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_10_16_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_10_16_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_10_16_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_10_16_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_10_16_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_10_16_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_10_16_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_10_16_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_11_0_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_11_0_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_11_0_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_11_0_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_11_0_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_11_0_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_11_0_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_11_0_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_11_0_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_11_0_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_11_0_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_11_0_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_11_0_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_11_0_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_11_0_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_11_0_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_11_0_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_11_1_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_11_1_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_11_1_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_11_1_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_11_1_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_11_1_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_11_1_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_11_1_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_11_1_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_11_1_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_11_1_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_11_1_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_11_1_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_11_1_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_11_1_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_11_1_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_11_1_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_11_2_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_11_2_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_11_2_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_11_2_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_11_2_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_11_2_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_11_2_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_11_2_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_11_2_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_11_2_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_11_2_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_11_2_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_11_2_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_11_2_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_11_2_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_11_2_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_11_2_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_11_3_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_11_3_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_11_3_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_11_3_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_11_3_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_11_3_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_11_3_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_11_3_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_11_3_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_11_3_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_11_3_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_11_3_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_11_3_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_11_3_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_11_3_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_11_3_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_11_3_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_11_4_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_11_4_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_11_4_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_11_4_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_11_4_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_11_4_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_11_4_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_11_4_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_11_4_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_11_4_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_11_4_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_11_4_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_11_4_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_11_4_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_11_4_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_11_4_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_11_4_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_11_5_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_11_5_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_11_5_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_11_5_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_11_5_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_11_5_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_11_5_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_11_5_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_11_5_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_11_5_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_11_5_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_11_5_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_11_5_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_11_5_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_11_5_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_11_5_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_11_5_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_11_6_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_11_6_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_11_6_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_11_6_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_11_6_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_11_6_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_11_6_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_11_6_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_11_6_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_11_6_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_11_6_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_11_6_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_11_6_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_11_6_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_11_6_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_11_6_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_11_6_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_11_7_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_11_7_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_11_7_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_11_7_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_11_7_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_11_7_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_11_7_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_11_7_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_11_7_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_11_7_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_11_7_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_11_7_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_11_7_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_11_7_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_11_7_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_11_7_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_11_7_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_11_8_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_11_8_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_11_8_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_11_8_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_11_8_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_11_8_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_11_8_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_11_8_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_11_8_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_11_8_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_11_8_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_11_8_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_11_8_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_11_8_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_11_8_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_11_8_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_11_8_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_11_9_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_11_9_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_11_9_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_11_9_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_11_9_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_11_9_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_11_9_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_11_9_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_11_9_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_11_9_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_11_9_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_11_9_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_11_9_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_11_9_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_11_9_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_11_9_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_11_9_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_11_10_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_11_10_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_11_10_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_11_10_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_11_10_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_11_10_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_11_10_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_11_10_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_11_10_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_11_10_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_11_10_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_11_10_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_11_10_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_11_10_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_11_10_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_11_10_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_11_10_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_11_11_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_11_11_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_11_11_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_11_11_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_11_11_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_11_11_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_11_11_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_11_11_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_11_11_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_11_11_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_11_11_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_11_11_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_11_11_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_11_11_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_11_11_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_11_11_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_11_11_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_11_12_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_11_12_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_11_12_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_11_12_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_11_12_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_11_12_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_11_12_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_11_12_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_11_12_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_11_12_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_11_12_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_11_12_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_11_12_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_11_12_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_11_12_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_11_12_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_11_12_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_11_13_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_11_13_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_11_13_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_11_13_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_11_13_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_11_13_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_11_13_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_11_13_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_11_13_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_11_13_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_11_13_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_11_13_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_11_13_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_11_13_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_11_13_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_11_13_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_11_13_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_11_14_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_11_14_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_11_14_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_11_14_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_11_14_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_11_14_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_11_14_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_11_14_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_11_14_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_11_14_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_11_14_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_11_14_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_11_14_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_11_14_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_11_14_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_11_14_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_11_14_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_11_15_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_11_15_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_11_15_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_11_15_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_11_15_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_11_15_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_11_15_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_11_15_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_11_15_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_11_15_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_11_15_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_11_15_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_11_15_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_11_15_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_11_15_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_11_15_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_11_15_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_11_16_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_11_16_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_11_16_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_11_16_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_11_16_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_11_16_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_11_16_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_11_16_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_11_16_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_11_16_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_11_16_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_11_16_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_11_16_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_11_16_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_11_16_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_11_16_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_11_16_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_12_0_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_12_0_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_12_0_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_12_0_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_12_0_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_12_0_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_12_0_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_12_0_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_12_0_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_12_0_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_12_0_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_12_0_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_12_0_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_12_0_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_12_0_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_12_0_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_12_0_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_12_1_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_12_1_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_12_1_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_12_1_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_12_1_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_12_1_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_12_1_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_12_1_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_12_1_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_12_1_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_12_1_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_12_1_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_12_1_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_12_1_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_12_1_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_12_1_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_12_1_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_12_2_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_12_2_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_12_2_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_12_2_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_12_2_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_12_2_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_12_2_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_12_2_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_12_2_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_12_2_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_12_2_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_12_2_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_12_2_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_12_2_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_12_2_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_12_2_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_12_2_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_12_3_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_12_3_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_12_3_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_12_3_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_12_3_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_12_3_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_12_3_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_12_3_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_12_3_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_12_3_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_12_3_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_12_3_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_12_3_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_12_3_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_12_3_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_12_3_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_12_3_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_12_4_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_12_4_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_12_4_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_12_4_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_12_4_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_12_4_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_12_4_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_12_4_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_12_4_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_12_4_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_12_4_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_12_4_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_12_4_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_12_4_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_12_4_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_12_4_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_12_4_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_12_5_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_12_5_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_12_5_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_12_5_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_12_5_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_12_5_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_12_5_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_12_5_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_12_5_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_12_5_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_12_5_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_12_5_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_12_5_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_12_5_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_12_5_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_12_5_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_12_5_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_12_6_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_12_6_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_12_6_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_12_6_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_12_6_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_12_6_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_12_6_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_12_6_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_12_6_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_12_6_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_12_6_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_12_6_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_12_6_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_12_6_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_12_6_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_12_6_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_12_6_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_12_7_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_12_7_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_12_7_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_12_7_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_12_7_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_12_7_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_12_7_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_12_7_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_12_7_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_12_7_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_12_7_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_12_7_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_12_7_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_12_7_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_12_7_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_12_7_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_12_7_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_12_8_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_12_8_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_12_8_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_12_8_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_12_8_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_12_8_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_12_8_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_12_8_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_12_8_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_12_8_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_12_8_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_12_8_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_12_8_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_12_8_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_12_8_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_12_8_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_12_8_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_12_9_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_12_9_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_12_9_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_12_9_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_12_9_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_12_9_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_12_9_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_12_9_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_12_9_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_12_9_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_12_9_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_12_9_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_12_9_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_12_9_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_12_9_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_12_9_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_12_9_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_12_10_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_12_10_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_12_10_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_12_10_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_12_10_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_12_10_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_12_10_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_12_10_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_12_10_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_12_10_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_12_10_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_12_10_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_12_10_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_12_10_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_12_10_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_12_10_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_12_10_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_12_11_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_12_11_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_12_11_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_12_11_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_12_11_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_12_11_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_12_11_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_12_11_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_12_11_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_12_11_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_12_11_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_12_11_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_12_11_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_12_11_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_12_11_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_12_11_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_12_11_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_12_12_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_12_12_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_12_12_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_12_12_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_12_12_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_12_12_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_12_12_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_12_12_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_12_12_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_12_12_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_12_12_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_12_12_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_12_12_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_12_12_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_12_12_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_12_12_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_12_12_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_12_13_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_12_13_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_12_13_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_12_13_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_12_13_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_12_13_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_12_13_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_12_13_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_12_13_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_12_13_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_12_13_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_12_13_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_12_13_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_12_13_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_12_13_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_12_13_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_12_13_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_12_14_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_12_14_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_12_14_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_12_14_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_12_14_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_12_14_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_12_14_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_12_14_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_12_14_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_12_14_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_12_14_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_12_14_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_12_14_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_12_14_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_12_14_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_12_14_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_12_14_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_12_15_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_12_15_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_12_15_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_12_15_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_12_15_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_12_15_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_12_15_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_12_15_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_12_15_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_12_15_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_12_15_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_12_15_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_12_15_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_12_15_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_12_15_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_12_15_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_12_15_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_12_16_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_12_16_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_12_16_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_12_16_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_12_16_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_12_16_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_12_16_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_12_16_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_12_16_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_12_16_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_12_16_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_12_16_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_12_16_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_12_16_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_12_16_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_12_16_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_12_16_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_13_0_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_13_0_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_13_0_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_13_0_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_13_0_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_13_0_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_13_0_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_13_0_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_13_0_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_13_0_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_13_0_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_13_0_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_13_0_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_13_0_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_13_0_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_13_0_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_13_0_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_13_1_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_13_1_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_13_1_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_13_1_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_13_1_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_13_1_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_13_1_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_13_1_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_13_1_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_13_1_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_13_1_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_13_1_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_13_1_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_13_1_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_13_1_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_13_1_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_13_1_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_13_2_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_13_2_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_13_2_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_13_2_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_13_2_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_13_2_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_13_2_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_13_2_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_13_2_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_13_2_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_13_2_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_13_2_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_13_2_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_13_2_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_13_2_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_13_2_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_13_2_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_13_3_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_13_3_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_13_3_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_13_3_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_13_3_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_13_3_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_13_3_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_13_3_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_13_3_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_13_3_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_13_3_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_13_3_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_13_3_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_13_3_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_13_3_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_13_3_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_13_3_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_13_4_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_13_4_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_13_4_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_13_4_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_13_4_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_13_4_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_13_4_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_13_4_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_13_4_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_13_4_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_13_4_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_13_4_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_13_4_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_13_4_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_13_4_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_13_4_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_13_4_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_13_5_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_13_5_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_13_5_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_13_5_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_13_5_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_13_5_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_13_5_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_13_5_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_13_5_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_13_5_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_13_5_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_13_5_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_13_5_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_13_5_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_13_5_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_13_5_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_13_5_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_13_6_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_13_6_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_13_6_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_13_6_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_13_6_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_13_6_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_13_6_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_13_6_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_13_6_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_13_6_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_13_6_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_13_6_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_13_6_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_13_6_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_13_6_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_13_6_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_13_6_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_13_7_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_13_7_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_13_7_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_13_7_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_13_7_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_13_7_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_13_7_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_13_7_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_13_7_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_13_7_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_13_7_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_13_7_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_13_7_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_13_7_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_13_7_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_13_7_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_13_7_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_13_8_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_13_8_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_13_8_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_13_8_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_13_8_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_13_8_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_13_8_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_13_8_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_13_8_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_13_8_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_13_8_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_13_8_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_13_8_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_13_8_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_13_8_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_13_8_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_13_8_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_13_9_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_13_9_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_13_9_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_13_9_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_13_9_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_13_9_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_13_9_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_13_9_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_13_9_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_13_9_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_13_9_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_13_9_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_13_9_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_13_9_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_13_9_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_13_9_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_13_9_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_13_10_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_13_10_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_13_10_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_13_10_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_13_10_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_13_10_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_13_10_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_13_10_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_13_10_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_13_10_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_13_10_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_13_10_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_13_10_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_13_10_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_13_10_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_13_10_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_13_10_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_13_11_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_13_11_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_13_11_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_13_11_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_13_11_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_13_11_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_13_11_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_13_11_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_13_11_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_13_11_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_13_11_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_13_11_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_13_11_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_13_11_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_13_11_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_13_11_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_13_11_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_13_12_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_13_12_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_13_12_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_13_12_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_13_12_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_13_12_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_13_12_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_13_12_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_13_12_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_13_12_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_13_12_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_13_12_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_13_12_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_13_12_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_13_12_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_13_12_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_13_12_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_13_13_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_13_13_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_13_13_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_13_13_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_13_13_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_13_13_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_13_13_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_13_13_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_13_13_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_13_13_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_13_13_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_13_13_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_13_13_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_13_13_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_13_13_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_13_13_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_13_13_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_13_14_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_13_14_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_13_14_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_13_14_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_13_14_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_13_14_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_13_14_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_13_14_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_13_14_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_13_14_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_13_14_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_13_14_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_13_14_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_13_14_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_13_14_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_13_14_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_13_14_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_13_15_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_13_15_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_13_15_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_13_15_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_13_15_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_13_15_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_13_15_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_13_15_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_13_15_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_13_15_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_13_15_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_13_15_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_13_15_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_13_15_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_13_15_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_13_15_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_13_15_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_13_16_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_13_16_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_13_16_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_13_16_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_13_16_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_13_16_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_13_16_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_13_16_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_13_16_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_13_16_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_13_16_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_13_16_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_13_16_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_13_16_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_13_16_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_13_16_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_13_16_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_14_0_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_14_0_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_14_0_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_14_0_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_14_0_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_14_0_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_14_0_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_14_0_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_14_0_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_14_0_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_14_0_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_14_0_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_14_0_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_14_0_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_14_0_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_14_0_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_14_0_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_14_1_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_14_1_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_14_1_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_14_1_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_14_1_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_14_1_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_14_1_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_14_1_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_14_1_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_14_1_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_14_1_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_14_1_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_14_1_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_14_1_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_14_1_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_14_1_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_14_1_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_14_2_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_14_2_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_14_2_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_14_2_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_14_2_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_14_2_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_14_2_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_14_2_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_14_2_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_14_2_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_14_2_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_14_2_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_14_2_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_14_2_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_14_2_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_14_2_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_14_2_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_14_3_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_14_3_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_14_3_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_14_3_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_14_3_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_14_3_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_14_3_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_14_3_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_14_3_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_14_3_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_14_3_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_14_3_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_14_3_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_14_3_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_14_3_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_14_3_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_14_3_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_14_4_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_14_4_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_14_4_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_14_4_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_14_4_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_14_4_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_14_4_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_14_4_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_14_4_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_14_4_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_14_4_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_14_4_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_14_4_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_14_4_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_14_4_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_14_4_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_14_4_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_14_5_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_14_5_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_14_5_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_14_5_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_14_5_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_14_5_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_14_5_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_14_5_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_14_5_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_14_5_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_14_5_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_14_5_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_14_5_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_14_5_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_14_5_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_14_5_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_14_5_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_14_6_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_14_6_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_14_6_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_14_6_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_14_6_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_14_6_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_14_6_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_14_6_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_14_6_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_14_6_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_14_6_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_14_6_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_14_6_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_14_6_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_14_6_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_14_6_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_14_6_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_14_7_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_14_7_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_14_7_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_14_7_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_14_7_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_14_7_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_14_7_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_14_7_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_14_7_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_14_7_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_14_7_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_14_7_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_14_7_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_14_7_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_14_7_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_14_7_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_14_7_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_14_8_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_14_8_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_14_8_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_14_8_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_14_8_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_14_8_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_14_8_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_14_8_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_14_8_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_14_8_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_14_8_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_14_8_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_14_8_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_14_8_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_14_8_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_14_8_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_14_8_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_14_9_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_14_9_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_14_9_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_14_9_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_14_9_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_14_9_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_14_9_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_14_9_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_14_9_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_14_9_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_14_9_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_14_9_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_14_9_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_14_9_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_14_9_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_14_9_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_14_9_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_14_10_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_14_10_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_14_10_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_14_10_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_14_10_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_14_10_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_14_10_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_14_10_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_14_10_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_14_10_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_14_10_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_14_10_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_14_10_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_14_10_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_14_10_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_14_10_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_14_10_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_14_11_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_14_11_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_14_11_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_14_11_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_14_11_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_14_11_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_14_11_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_14_11_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_14_11_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_14_11_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_14_11_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_14_11_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_14_11_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_14_11_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_14_11_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_14_11_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_14_11_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_14_12_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_14_12_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_14_12_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_14_12_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_14_12_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_14_12_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_14_12_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_14_12_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_14_12_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_14_12_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_14_12_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_14_12_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_14_12_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_14_12_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_14_12_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_14_12_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_14_12_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_14_13_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_14_13_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_14_13_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_14_13_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_14_13_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_14_13_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_14_13_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_14_13_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_14_13_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_14_13_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_14_13_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_14_13_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_14_13_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_14_13_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_14_13_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_14_13_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_14_13_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_14_14_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_14_14_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_14_14_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_14_14_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_14_14_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_14_14_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_14_14_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_14_14_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_14_14_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_14_14_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_14_14_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_14_14_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_14_14_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_14_14_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_14_14_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_14_14_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_14_14_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_14_15_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_14_15_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_14_15_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_14_15_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_14_15_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_14_15_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_14_15_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_14_15_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_14_15_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_14_15_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_14_15_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_14_15_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_14_15_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_14_15_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_14_15_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_14_15_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_14_15_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_14_16_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_14_16_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_14_16_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_14_16_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_14_16_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_14_16_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_14_16_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_14_16_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_14_16_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_14_16_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_14_16_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_14_16_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_14_16_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_14_16_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_14_16_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_14_16_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_14_16_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_15_0_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_15_0_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_15_0_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_15_0_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_15_0_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_15_0_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_15_0_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_15_0_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_15_0_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_15_0_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_15_0_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_15_0_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_15_0_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_15_0_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_15_0_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_15_0_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_15_0_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_15_1_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_15_1_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_15_1_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_15_1_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_15_1_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_15_1_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_15_1_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_15_1_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_15_1_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_15_1_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_15_1_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_15_1_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_15_1_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_15_1_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_15_1_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_15_1_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_15_1_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_15_2_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_15_2_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_15_2_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_15_2_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_15_2_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_15_2_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_15_2_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_15_2_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_15_2_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_15_2_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_15_2_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_15_2_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_15_2_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_15_2_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_15_2_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_15_2_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_15_2_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_15_3_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_15_3_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_15_3_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_15_3_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_15_3_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_15_3_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_15_3_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_15_3_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_15_3_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_15_3_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_15_3_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_15_3_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_15_3_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_15_3_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_15_3_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_15_3_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_15_3_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_15_4_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_15_4_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_15_4_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_15_4_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_15_4_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_15_4_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_15_4_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_15_4_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_15_4_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_15_4_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_15_4_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_15_4_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_15_4_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_15_4_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_15_4_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_15_4_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_15_4_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_15_5_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_15_5_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_15_5_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_15_5_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_15_5_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_15_5_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_15_5_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_15_5_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_15_5_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_15_5_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_15_5_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_15_5_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_15_5_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_15_5_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_15_5_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_15_5_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_15_5_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_15_6_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_15_6_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_15_6_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_15_6_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_15_6_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_15_6_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_15_6_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_15_6_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_15_6_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_15_6_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_15_6_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_15_6_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_15_6_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_15_6_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_15_6_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_15_6_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_15_6_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_15_7_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_15_7_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_15_7_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_15_7_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_15_7_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_15_7_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_15_7_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_15_7_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_15_7_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_15_7_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_15_7_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_15_7_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_15_7_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_15_7_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_15_7_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_15_7_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_15_7_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_15_8_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_15_8_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_15_8_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_15_8_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_15_8_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_15_8_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_15_8_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_15_8_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_15_8_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_15_8_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_15_8_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_15_8_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_15_8_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_15_8_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_15_8_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_15_8_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_15_8_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_15_9_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_15_9_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_15_9_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_15_9_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_15_9_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_15_9_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_15_9_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_15_9_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_15_9_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_15_9_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_15_9_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_15_9_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_15_9_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_15_9_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_15_9_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_15_9_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_15_9_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_15_10_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_15_10_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_15_10_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_15_10_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_15_10_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_15_10_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_15_10_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_15_10_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_15_10_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_15_10_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_15_10_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_15_10_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_15_10_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_15_10_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_15_10_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_15_10_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_15_10_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_15_11_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_15_11_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_15_11_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_15_11_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_15_11_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_15_11_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_15_11_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_15_11_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_15_11_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_15_11_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_15_11_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_15_11_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_15_11_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_15_11_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_15_11_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_15_11_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_15_11_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_15_12_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_15_12_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_15_12_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_15_12_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_15_12_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_15_12_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_15_12_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_15_12_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_15_12_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_15_12_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_15_12_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_15_12_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_15_12_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_15_12_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_15_12_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_15_12_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_15_12_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_15_13_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_15_13_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_15_13_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_15_13_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_15_13_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_15_13_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_15_13_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_15_13_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_15_13_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_15_13_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_15_13_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_15_13_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_15_13_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_15_13_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_15_13_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_15_13_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_15_13_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_15_14_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_15_14_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_15_14_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_15_14_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_15_14_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_15_14_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_15_14_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_15_14_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_15_14_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_15_14_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_15_14_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_15_14_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_15_14_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_15_14_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_15_14_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_15_14_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_15_14_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_15_15_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_15_15_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_15_15_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_15_15_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_15_15_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_15_15_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_15_15_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_15_15_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_15_15_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_15_15_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_15_15_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_15_15_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_15_15_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_15_15_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_15_15_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_15_15_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_15_15_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_15_16_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_15_16_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_15_16_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_15_16_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_15_16_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_15_16_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_15_16_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_15_16_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_15_16_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_15_16_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_15_16_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_15_16_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_15_16_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_15_16_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_15_16_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_15_16_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_15_16_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_16_0_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_16_0_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_16_0_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_16_0_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_16_0_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_16_0_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_16_0_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_16_0_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_16_0_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_16_0_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_16_0_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_16_0_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_16_0_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_16_0_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_16_0_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_16_0_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_16_0_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_16_1_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_16_1_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_16_1_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_16_1_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_16_1_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_16_1_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_16_1_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_16_1_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_16_1_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_16_1_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_16_1_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_16_1_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_16_1_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_16_1_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_16_1_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_16_1_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_16_1_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_16_2_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_16_2_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_16_2_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_16_2_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_16_2_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_16_2_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_16_2_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_16_2_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_16_2_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_16_2_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_16_2_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_16_2_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_16_2_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_16_2_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_16_2_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_16_2_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_16_2_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_16_3_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_16_3_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_16_3_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_16_3_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_16_3_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_16_3_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_16_3_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_16_3_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_16_3_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_16_3_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_16_3_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_16_3_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_16_3_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_16_3_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_16_3_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_16_3_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_16_3_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_16_4_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_16_4_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_16_4_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_16_4_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_16_4_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_16_4_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_16_4_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_16_4_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_16_4_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_16_4_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_16_4_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_16_4_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_16_4_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_16_4_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_16_4_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_16_4_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_16_4_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_16_5_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_16_5_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_16_5_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_16_5_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_16_5_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_16_5_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_16_5_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_16_5_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_16_5_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_16_5_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_16_5_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_16_5_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_16_5_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_16_5_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_16_5_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_16_5_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_16_5_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_16_6_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_16_6_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_16_6_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_16_6_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_16_6_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_16_6_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_16_6_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_16_6_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_16_6_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_16_6_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_16_6_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_16_6_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_16_6_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_16_6_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_16_6_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_16_6_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_16_6_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_16_7_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_16_7_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_16_7_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_16_7_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_16_7_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_16_7_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_16_7_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_16_7_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_16_7_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_16_7_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_16_7_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_16_7_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_16_7_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_16_7_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_16_7_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_16_7_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_16_7_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_16_8_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_16_8_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_16_8_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_16_8_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_16_8_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_16_8_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_16_8_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_16_8_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_16_8_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_16_8_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_16_8_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_16_8_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_16_8_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_16_8_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_16_8_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_16_8_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_16_8_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_16_9_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_16_9_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_16_9_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_16_9_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_16_9_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_16_9_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_16_9_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_16_9_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_16_9_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_16_9_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_16_9_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_16_9_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_16_9_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_16_9_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_16_9_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_16_9_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_16_9_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_16_10_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_16_10_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_16_10_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_16_10_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_16_10_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_16_10_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_16_10_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_16_10_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_16_10_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_16_10_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_16_10_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_16_10_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_16_10_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_16_10_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_16_10_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_16_10_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_16_10_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_16_11_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_16_11_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_16_11_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_16_11_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_16_11_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_16_11_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_16_11_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_16_11_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_16_11_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_16_11_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_16_11_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_16_11_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_16_11_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_16_11_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_16_11_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_16_11_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_16_11_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_16_12_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_16_12_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_16_12_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_16_12_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_16_12_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_16_12_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_16_12_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_16_12_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_16_12_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_16_12_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_16_12_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_16_12_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_16_12_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_16_12_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_16_12_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_16_12_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_16_12_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_16_13_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_16_13_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_16_13_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_16_13_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_16_13_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_16_13_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_16_13_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_16_13_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_16_13_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_16_13_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_16_13_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_16_13_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_16_13_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_16_13_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_16_13_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_16_13_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_16_13_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_16_14_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_16_14_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_16_14_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_16_14_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_16_14_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_16_14_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_16_14_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_16_14_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_16_14_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_16_14_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_16_14_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_16_14_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_16_14_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_16_14_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_16_14_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_16_14_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_16_14_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_16_15_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_16_15_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_16_15_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_16_15_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_16_15_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_16_15_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_16_15_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_16_15_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_16_15_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_16_15_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_16_15_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_16_15_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_16_15_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_16_15_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_16_15_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_16_15_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_16_15_r16⟩
  · rcases (by omega : (0 ≤ a2 ∧ a2 < 1) ∨ (1 ≤ a2 ∧ a2 < 2) ∨ (2 ≤ a2 ∧ a2 < 3) ∨ (3 ≤ a2 ∧ a2 < 4) ∨ (4 ≤ a2 ∧ a2 < 5) ∨ (5 ≤ a2 ∧ a2 < 6) ∨ (6 ≤ a2 ∧ a2 < 7) ∨ (7 ≤ a2 ∧ a2 < 8) ∨ (8 ≤ a2 ∧ a2 < 9) ∨ (9 ≤ a2 ∧ a2 < 10) ∨ (10 ≤ a2 ∧ a2 < 11) ∨ (11 ≤ a2 ∧ a2 < 12) ∨ (12 ≤ a2 ∧ a2 < 13) ∨ (13 ≤ a2 ∧ a2 < 14) ∨ (14 ≤ a2 ∧ a2 < 15) ∨ (15 ≤ a2 ∧ a2 < 16) ∨ (16 ≤ a2 ∧ a2 < 17)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, 1, h.1, by omega, by norm_num, ubc_16_16_r0⟩
    · exact ⟨1, 1, h.1, by omega, by norm_num, ubc_16_16_r1⟩
    · exact ⟨2, 1, h.1, by omega, by norm_num, ubc_16_16_r2⟩
    · exact ⟨3, 1, h.1, by omega, by norm_num, ubc_16_16_r3⟩
    · exact ⟨4, 1, h.1, by omega, by norm_num, ubc_16_16_r4⟩
    · exact ⟨5, 1, h.1, by omega, by norm_num, ubc_16_16_r5⟩
    · exact ⟨6, 1, h.1, by omega, by norm_num, ubc_16_16_r6⟩
    · exact ⟨7, 1, h.1, by omega, by norm_num, ubc_16_16_r7⟩
    · exact ⟨8, 1, h.1, by omega, by norm_num, ubc_16_16_r8⟩
    · exact ⟨9, 1, h.1, by omega, by norm_num, ubc_16_16_r9⟩
    · exact ⟨10, 1, h.1, by omega, by norm_num, ubc_16_16_r10⟩
    · exact ⟨11, 1, h.1, by omega, by norm_num, ubc_16_16_r11⟩
    · exact ⟨12, 1, h.1, by omega, by norm_num, ubc_16_16_r12⟩
    · exact ⟨13, 1, h.1, by omega, by norm_num, ubc_16_16_r13⟩
    · exact ⟨14, 1, h.1, by omega, by norm_num, ubc_16_16_r14⟩
    · exact ⟨15, 1, h.1, by omega, by norm_num, ubc_16_16_r15⟩
    · exact ⟨16, 1, h.1, by omega, by norm_num, ubc_16_16_r16⟩
theorem TTr_0 : (List.range 39).all (fun k => tRowOK UBT (nS 1 6) (pairsU (x2Mult 1 6)) ((pairsU (x2Mult 1 6)).getD (0 + k) (0, 0)) (TT.getD (0 + k) [])) = true := by decide +kernel
theorem TTr_39 : (List.range 39).all (fun k => tRowOK UBT (nS 1 6) (pairsU (x2Mult 1 6)) ((pairsU (x2Mult 1 6)).getD (39 + k) (0, 0)) (TT.getD (39 + k) [])) = true := by decide +kernel
theorem TTr_78 : (List.range 39).all (fun k => tRowOK UBT (nS 1 6) (pairsU (x2Mult 1 6)) ((pairsU (x2Mult 1 6)).getD (78 + k) (0, 0)) (TT.getD (78 + k) [])) = true := by decide +kernel
theorem TTr_117 : (List.range 36).all (fun k => tRowOK UBT (nS 1 6) (pairsU (x2Mult 1 6)) ((pairsU (x2Mult 1 6)).getD (117 + k) (0, 0)) (TT.getD (117 + k) [])) = true := by decide +kernel
theorem TTrows : ∀ i < nS 1 6, tRowOK UBT (nS 1 6) (pairsU (x2Mult 1 6)) ((pairsU (x2Mult 1 6)).getD i (0, 0)) (TT.getD i []) = true := by
  show ∀ i < 153, tRowOK UBT (nS 1 6) (pairsU (x2Mult 1 6)) ((pairsU (x2Mult 1 6)).getD i (0, 0)) (TT.getD i []) = true
  intro i hi
  rcases (by omega : (0 ≤ i ∧ i < 39) ∨ (39 ≤ i ∧ i < 78) ∨ (78 ≤ i ∧ i < 117) ∨ (117 ≤ i ∧ i < 153)) with h | h | h | h
  · exact rangeAll_sound (fun i => tRowOK UBT (nS 1 6) (pairsU (x2Mult 1 6)) ((pairsU (x2Mult 1 6)).getD i (0, 0)) (TT.getD i [])) 0 39 TTr_0 i h.1 (by omega)
  · exact rangeAll_sound (fun i => tRowOK UBT (nS 1 6) (pairsU (x2Mult 1 6)) ((pairsU (x2Mult 1 6)).getD i (0, 0)) (TT.getD i [])) 39 39 TTr_39 i h.1 (by omega)
  · exact rangeAll_sound (fun i => tRowOK UBT (nS 1 6) (pairsU (x2Mult 1 6)) ((pairsU (x2Mult 1 6)).getD i (0, 0)) (TT.getD i [])) 78 39 TTr_78 i h.1 (by omega)
  · exact rangeAll_sound (fun i => tRowOK UBT (nS 1 6) (pairsU (x2Mult 1 6)) ((pairsU (x2Mult 1 6)).getD i (0, 0)) (TT.getD i [])) 117 36 TTr_117 i h.1 (by omega)

theorem spec (N : X2Blocks 1) (hN : ∀ k, (N k)ᵀ = N k) (hN159 : N k159 = x2TrialForm 1 k159) (hN160 : N k160 = x2TrialForm 1 k160) (hN161 : N k161 = x2TrialForm 1 k161) :
    TTspecS 1 N 6 6 6 TT ∧ TCspecS 1 N 6 6 6 TT := by
  have hk := keys N hN159 hN160 hN161
  have htt := tripleSpecS' 1 (by decide) N hN 6 6 6 (by decide) (by decide) ks hks hnd hk hlen UBT shape hchk (fun i0 i1 => (TT.getD i1 []).getD i0 0) (tTT_of_rows 1 (by decide) UBT 6 6 6 TT TTrows)
  exact ⟨htt, tcSpec_of_tt_eq 1 N 6 6 TT htt⟩

end ThreeCopyQutritWerner.X2.InK1x666
