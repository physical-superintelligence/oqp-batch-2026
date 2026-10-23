module

public import ThreeCopyQutritWerner.CertificateLocalGenerators

@[expose] public section


/-!
Exact signed weights and two raising equations for all 22 archive local frames. Every assertion
is an ordinary kernel `decide` check on finite integer support lists. These
equations do not assert descendant completeness or endpoint positivity.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

open scoped Matrix

namespace ThreeCopyQutritWerner

/-- Sector 0, type 0: the declared signed highest weight on physical rows. -/
theorem certificateLocalFrame0_0_weight (w : CertificateLocalWord)
    (c : Fin 1) (i : Fin 3) :
    certificateLocalWeight {5} w i * certificateLocalFrame0_0 w c =
      (![1, 0, -5] : Fin 3 → ℤ) i * certificateLocalFrame0_0 w c := by
  exact certificateLocalFrame_weight_of_check {5} ![1, 0, -5]
    certificateLocalFrameEntries0_0 c (by fin_cases c <;> decide) i w

/-- Sector 0, type 0: the literal signed E01 annihilates every column. -/
theorem certificateLocalFrame0_0_raising01 :
    certificateLocalGenerator {5} 0 1 * certificateLocalFrame0_0 = 0 := by
  have hc : ∀ c : Fin 1, certificateLocalGenerator {5} 0 1 *ᵥ
      (fun w => certificateLocalFrame0_0 w c) = 0 := by
    intro c
    apply certificateLocalGenerator_annihilates_of_check
    fin_cases c <;> decide
  ext w c
  exact congrFun (hc c) w

/-- Sector 0, type 0: the literal signed E12 annihilates every column. -/
theorem certificateLocalFrame0_0_raising12 :
    certificateLocalGenerator {5} 1 2 * certificateLocalFrame0_0 = 0 := by
  have hc : ∀ c : Fin 1, certificateLocalGenerator {5} 1 2 *ᵥ
      (fun w => certificateLocalFrame0_0 w c) = 0 := by
    intro c
    apply certificateLocalGenerator_annihilates_of_check
    fin_cases c <;> decide
  ext w c
  exact congrFun (hc c) w

/-- Sector 0, type 1: the declared signed highest weight on physical rows. -/
theorem certificateLocalFrame0_1_weight (w : CertificateLocalWord)
    (c : Fin 4) (i : Fin 3) :
    certificateLocalWeight {5} w i * certificateLocalFrame0_1 w c =
      (![1, -1, -4] : Fin 3 → ℤ) i * certificateLocalFrame0_1 w c := by
  exact certificateLocalFrame_weight_of_check {5} ![1, -1, -4]
    certificateLocalFrameEntries0_1 c (by fin_cases c <;> decide) i w

/-- Sector 0, type 1: the literal signed E01 annihilates every column. -/
theorem certificateLocalFrame0_1_raising01 :
    certificateLocalGenerator {5} 0 1 * certificateLocalFrame0_1 = 0 := by
  have hc : ∀ c : Fin 4, certificateLocalGenerator {5} 0 1 *ᵥ
      (fun w => certificateLocalFrame0_1 w c) = 0 := by
    intro c
    apply certificateLocalGenerator_annihilates_of_check
    fin_cases c <;> decide
  ext w c
  exact congrFun (hc c) w

/-- Sector 0, type 1: the literal signed E12 annihilates every column. -/
theorem certificateLocalFrame0_1_raising12 :
    certificateLocalGenerator {5} 1 2 * certificateLocalFrame0_1 = 0 := by
  have hc : ∀ c : Fin 4, certificateLocalGenerator {5} 1 2 *ᵥ
      (fun w => certificateLocalFrame0_1 w c) = 0 := by
    intro c
    apply certificateLocalGenerator_annihilates_of_check
    fin_cases c <;> decide
  ext w c
  exact congrFun (hc c) w

/-- Sector 0, type 2: the declared signed highest weight on physical rows. -/
theorem certificateLocalFrame0_2_weight (w : CertificateLocalWord)
    (c : Fin 5) (i : Fin 3) :
    certificateLocalWeight {5} w i * certificateLocalFrame0_2 w c =
      (![0, 0, -4] : Fin 3 → ℤ) i * certificateLocalFrame0_2 w c := by
  exact certificateLocalFrame_weight_of_check {5} ![0, 0, -4]
    certificateLocalFrameEntries0_2 c (by fin_cases c <;> decide) i w

/-- Sector 0, type 2: the literal signed E01 annihilates every column. -/
theorem certificateLocalFrame0_2_raising01 :
    certificateLocalGenerator {5} 0 1 * certificateLocalFrame0_2 = 0 := by
  have hc : ∀ c : Fin 5, certificateLocalGenerator {5} 0 1 *ᵥ
      (fun w => certificateLocalFrame0_2 w c) = 0 := by
    intro c
    apply certificateLocalGenerator_annihilates_of_check
    fin_cases c <;> decide
  ext w c
  exact congrFun (hc c) w

/-- Sector 0, type 2: the literal signed E12 annihilates every column. -/
theorem certificateLocalFrame0_2_raising12 :
    certificateLocalGenerator {5} 1 2 * certificateLocalFrame0_2 = 0 := by
  have hc : ∀ c : Fin 5, certificateLocalGenerator {5} 1 2 *ᵥ
      (fun w => certificateLocalFrame0_2 w c) = 0 := by
    intro c
    apply certificateLocalGenerator_annihilates_of_check
    fin_cases c <;> decide
  ext w c
  exact congrFun (hc c) w

/-- Sector 0, type 3: the declared signed highest weight on physical rows. -/
theorem certificateLocalFrame0_3_weight (w : CertificateLocalWord)
    (c : Fin 5) (i : Fin 3) :
    certificateLocalWeight {5} w i * certificateLocalFrame0_3 w c =
      (![1, -2, -3] : Fin 3 → ℤ) i * certificateLocalFrame0_3 w c := by
  exact certificateLocalFrame_weight_of_check {5} ![1, -2, -3]
    certificateLocalFrameEntries0_3 c (by fin_cases c <;> decide) i w

/-- Sector 0, type 3: the literal signed E01 annihilates every column. -/
theorem certificateLocalFrame0_3_raising01 :
    certificateLocalGenerator {5} 0 1 * certificateLocalFrame0_3 = 0 := by
  have hc : ∀ c : Fin 5, certificateLocalGenerator {5} 0 1 *ᵥ
      (fun w => certificateLocalFrame0_3 w c) = 0 := by
    intro c
    apply certificateLocalGenerator_annihilates_of_check
    fin_cases c <;> decide
  ext w c
  exact congrFun (hc c) w

/-- Sector 0, type 3: the literal signed E12 annihilates every column. -/
theorem certificateLocalFrame0_3_raising12 :
    certificateLocalGenerator {5} 1 2 * certificateLocalFrame0_3 = 0 := by
  have hc : ∀ c : Fin 5, certificateLocalGenerator {5} 1 2 *ᵥ
      (fun w => certificateLocalFrame0_3 w c) = 0 := by
    intro c
    apply certificateLocalGenerator_annihilates_of_check
    fin_cases c <;> decide
  ext w c
  exact congrFun (hc c) w

/-- Sector 0, type 4: the declared signed highest weight on physical rows. -/
theorem certificateLocalFrame0_4_weight (w : CertificateLocalWord)
    (c : Fin 15) (i : Fin 3) :
    certificateLocalWeight {5} w i * certificateLocalFrame0_4 w c =
      (![0, -1, -3] : Fin 3 → ℤ) i * certificateLocalFrame0_4 w c := by
  exact certificateLocalFrame_weight_of_check {5} ![0, -1, -3]
    certificateLocalFrameEntries0_4 c (by fin_cases c <;> decide) i w

/-- Sector 0, type 4: the literal signed E01 annihilates every column. -/
theorem certificateLocalFrame0_4_raising01 :
    certificateLocalGenerator {5} 0 1 * certificateLocalFrame0_4 = 0 := by
  have hc : ∀ c : Fin 15, certificateLocalGenerator {5} 0 1 *ᵥ
      (fun w => certificateLocalFrame0_4 w c) = 0 := by
    intro c
    apply certificateLocalGenerator_annihilates_of_check
    fin_cases c <;> decide
  ext w c
  exact congrFun (hc c) w

/-- Sector 0, type 4: the literal signed E12 annihilates every column. -/
theorem certificateLocalFrame0_4_raising12 :
    certificateLocalGenerator {5} 1 2 * certificateLocalFrame0_4 = 0 := by
  have hc : ∀ c : Fin 15, certificateLocalGenerator {5} 1 2 *ᵥ
      (fun w => certificateLocalFrame0_4 w c) = 0 := by
    intro c
    apply certificateLocalGenerator_annihilates_of_check
    fin_cases c <;> decide
  ext w c
  exact congrFun (hc c) w

/-- Sector 0, type 5: the declared signed highest weight on physical rows. -/
theorem certificateLocalFrame0_5_weight (w : CertificateLocalWord)
    (c : Fin 10) (i : Fin 3) :
    certificateLocalWeight {5} w i * certificateLocalFrame0_5 w c =
      (![0, -2, -2] : Fin 3 → ℤ) i * certificateLocalFrame0_5 w c := by
  exact certificateLocalFrame_weight_of_check {5} ![0, -2, -2]
    certificateLocalFrameEntries0_5 c (by fin_cases c <;> decide) i w

/-- Sector 0, type 5: the literal signed E01 annihilates every column. -/
theorem certificateLocalFrame0_5_raising01 :
    certificateLocalGenerator {5} 0 1 * certificateLocalFrame0_5 = 0 := by
  have hc : ∀ c : Fin 10, certificateLocalGenerator {5} 0 1 *ᵥ
      (fun w => certificateLocalFrame0_5 w c) = 0 := by
    intro c
    apply certificateLocalGenerator_annihilates_of_check
    fin_cases c <;> decide
  ext w c
  exact congrFun (hc c) w

/-- Sector 0, type 5: the literal signed E12 annihilates every column. -/
theorem certificateLocalFrame0_5_raising12 :
    certificateLocalGenerator {5} 1 2 * certificateLocalFrame0_5 = 0 := by
  have hc : ∀ c : Fin 10, certificateLocalGenerator {5} 1 2 *ᵥ
      (fun w => certificateLocalFrame0_5 w c) = 0 := by
    intro c
    apply certificateLocalGenerator_annihilates_of_check
    fin_cases c <;> decide
  ext w c
  exact congrFun (hc c) w

/-- Sector 0, type 6: the declared signed highest weight on physical rows. -/
theorem certificateLocalFrame0_6_weight (w : CertificateLocalWord)
    (c : Fin 11) (i : Fin 3) :
    certificateLocalWeight {5} w i * certificateLocalFrame0_6 w c =
      (![-1, -1, -2] : Fin 3 → ℤ) i * certificateLocalFrame0_6 w c := by
  exact certificateLocalFrame_weight_of_check {5} ![-1, -1, -2]
    certificateLocalFrameEntries0_6 c (by fin_cases c <;> decide) i w

/-- Sector 0, type 6: the literal signed E01 annihilates every column. -/
theorem certificateLocalFrame0_6_raising01 :
    certificateLocalGenerator {5} 0 1 * certificateLocalFrame0_6 = 0 := by
  have hc : ∀ c : Fin 11, certificateLocalGenerator {5} 0 1 *ᵥ
      (fun w => certificateLocalFrame0_6 w c) = 0 := by
    intro c
    apply certificateLocalGenerator_annihilates_of_check
    fin_cases c <;> decide
  ext w c
  exact congrFun (hc c) w

/-- Sector 0, type 6: the literal signed E12 annihilates every column. -/
theorem certificateLocalFrame0_6_raising12 :
    certificateLocalGenerator {5} 1 2 * certificateLocalFrame0_6 = 0 := by
  have hc : ∀ c : Fin 11, certificateLocalGenerator {5} 1 2 *ᵥ
      (fun w => certificateLocalFrame0_6 w c) = 0 := by
    intro c
    apply certificateLocalGenerator_annihilates_of_check
    fin_cases c <;> decide
  ext w c
  exact congrFun (hc c) w

/-- Sector 1, type 0: the declared signed highest weight on physical rows. -/
theorem certificateLocalFrame1_0_weight (w : CertificateLocalWord)
    (c : Fin 1) (i : Fin 3) :
    certificateLocalWeight {0, 1, 2} w i * certificateLocalFrame1_0 w c =
      (![3, 0, -3] : Fin 3 → ℤ) i * certificateLocalFrame1_0 w c := by
  exact certificateLocalFrame_weight_of_check {0, 1, 2} ![3, 0, -3]
    certificateLocalFrameEntries1_0 c (by fin_cases c <;> decide) i w

/-- Sector 1, type 0: the literal signed E01 annihilates every column. -/
theorem certificateLocalFrame1_0_raising01 :
    certificateLocalGenerator {0, 1, 2} 0 1 * certificateLocalFrame1_0 = 0 := by
  have hc : ∀ c : Fin 1, certificateLocalGenerator {0, 1, 2} 0 1 *ᵥ
      (fun w => certificateLocalFrame1_0 w c) = 0 := by
    intro c
    apply certificateLocalGenerator_annihilates_of_check
    fin_cases c <;> decide
  ext w c
  exact congrFun (hc c) w

/-- Sector 1, type 0: the literal signed E12 annihilates every column. -/
theorem certificateLocalFrame1_0_raising12 :
    certificateLocalGenerator {0, 1, 2} 1 2 * certificateLocalFrame1_0 = 0 := by
  have hc : ∀ c : Fin 1, certificateLocalGenerator {0, 1, 2} 1 2 *ᵥ
      (fun w => certificateLocalFrame1_0 w c) = 0 := by
    intro c
    apply certificateLocalGenerator_annihilates_of_check
    fin_cases c <;> decide
  ext w c
  exact congrFun (hc c) w

/-- Sector 1, type 1: the declared signed highest weight on physical rows. -/
theorem certificateLocalFrame1_1_weight (w : CertificateLocalWord)
    (c : Fin 2) (i : Fin 3) :
    certificateLocalWeight {0, 1, 2} w i * certificateLocalFrame1_1 w c =
      (![3, -1, -2] : Fin 3 → ℤ) i * certificateLocalFrame1_1 w c := by
  exact certificateLocalFrame_weight_of_check {0, 1, 2} ![3, -1, -2]
    certificateLocalFrameEntries1_1 c (by fin_cases c <;> decide) i w

/-- Sector 1, type 1: the literal signed E01 annihilates every column. -/
theorem certificateLocalFrame1_1_raising01 :
    certificateLocalGenerator {0, 1, 2} 0 1 * certificateLocalFrame1_1 = 0 := by
  have hc : ∀ c : Fin 2, certificateLocalGenerator {0, 1, 2} 0 1 *ᵥ
      (fun w => certificateLocalFrame1_1 w c) = 0 := by
    intro c
    apply certificateLocalGenerator_annihilates_of_check
    fin_cases c <;> decide
  ext w c
  exact congrFun (hc c) w

/-- Sector 1, type 1: the literal signed E12 annihilates every column. -/
theorem certificateLocalFrame1_1_raising12 :
    certificateLocalGenerator {0, 1, 2} 1 2 * certificateLocalFrame1_1 = 0 := by
  have hc : ∀ c : Fin 2, certificateLocalGenerator {0, 1, 2} 1 2 *ᵥ
      (fun w => certificateLocalFrame1_1 w c) = 0 := by
    intro c
    apply certificateLocalGenerator_annihilates_of_check
    fin_cases c <;> decide
  ext w c
  exact congrFun (hc c) w

/-- Sector 1, type 2: the declared signed highest weight on physical rows. -/
theorem certificateLocalFrame1_2_weight (w : CertificateLocalWord)
    (c : Fin 2) (i : Fin 3) :
    certificateLocalWeight {0, 1, 2} w i * certificateLocalFrame1_2 w c =
      (![2, 1, -3] : Fin 3 → ℤ) i * certificateLocalFrame1_2 w c := by
  exact certificateLocalFrame_weight_of_check {0, 1, 2} ![2, 1, -3]
    certificateLocalFrameEntries1_2 c (by fin_cases c <;> decide) i w

/-- Sector 1, type 2: the literal signed E01 annihilates every column. -/
theorem certificateLocalFrame1_2_raising01 :
    certificateLocalGenerator {0, 1, 2} 0 1 * certificateLocalFrame1_2 = 0 := by
  have hc : ∀ c : Fin 2, certificateLocalGenerator {0, 1, 2} 0 1 *ᵥ
      (fun w => certificateLocalFrame1_2 w c) = 0 := by
    intro c
    apply certificateLocalGenerator_annihilates_of_check
    fin_cases c <;> decide
  ext w c
  exact congrFun (hc c) w

/-- Sector 1, type 2: the literal signed E12 annihilates every column. -/
theorem certificateLocalFrame1_2_raising12 :
    certificateLocalGenerator {0, 1, 2} 1 2 * certificateLocalFrame1_2 = 0 := by
  have hc : ∀ c : Fin 2, certificateLocalGenerator {0, 1, 2} 1 2 *ᵥ
      (fun w => certificateLocalFrame1_2 w c) = 0 := by
    intro c
    apply certificateLocalGenerator_annihilates_of_check
    fin_cases c <;> decide
  ext w c
  exact congrFun (hc c) w

/-- Sector 1, type 3: the declared signed highest weight on physical rows. -/
theorem certificateLocalFrame1_3_weight (w : CertificateLocalWord)
    (c : Fin 9) (i : Fin 3) :
    certificateLocalWeight {0, 1, 2} w i * certificateLocalFrame1_3 w c =
      (![2, 0, -2] : Fin 3 → ℤ) i * certificateLocalFrame1_3 w c := by
  exact certificateLocalFrame_weight_of_check {0, 1, 2} ![2, 0, -2]
    certificateLocalFrameEntries1_3 c (by fin_cases c <;> decide) i w

/-- Sector 1, type 3: the literal signed E01 annihilates every column. -/
theorem certificateLocalFrame1_3_raising01 :
    certificateLocalGenerator {0, 1, 2} 0 1 * certificateLocalFrame1_3 = 0 := by
  have hc : ∀ c : Fin 9, certificateLocalGenerator {0, 1, 2} 0 1 *ᵥ
      (fun w => certificateLocalFrame1_3 w c) = 0 := by
    intro c
    apply certificateLocalGenerator_annihilates_of_check
    fin_cases c <;> decide
  ext w c
  exact congrFun (hc c) w

/-- Sector 1, type 3: the literal signed E12 annihilates every column. -/
theorem certificateLocalFrame1_3_raising12 :
    certificateLocalGenerator {0, 1, 2} 1 2 * certificateLocalFrame1_3 = 0 := by
  have hc : ∀ c : Fin 9, certificateLocalGenerator {0, 1, 2} 1 2 *ᵥ
      (fun w => certificateLocalFrame1_3 w c) = 0 := by
    intro c
    apply certificateLocalGenerator_annihilates_of_check
    fin_cases c <;> decide
  ext w c
  exact congrFun (hc c) w

/-- Sector 1, type 4: the declared signed highest weight on physical rows. -/
theorem certificateLocalFrame1_4_weight (w : CertificateLocalWord)
    (c : Fin 7) (i : Fin 3) :
    certificateLocalWeight {0, 1, 2} w i * certificateLocalFrame1_4 w c =
      (![2, -1, -1] : Fin 3 → ℤ) i * certificateLocalFrame1_4 w c := by
  exact certificateLocalFrame_weight_of_check {0, 1, 2} ![2, -1, -1]
    certificateLocalFrameEntries1_4 c (by fin_cases c <;> decide) i w

/-- Sector 1, type 4: the literal signed E01 annihilates every column. -/
theorem certificateLocalFrame1_4_raising01 :
    certificateLocalGenerator {0, 1, 2} 0 1 * certificateLocalFrame1_4 = 0 := by
  have hc : ∀ c : Fin 7, certificateLocalGenerator {0, 1, 2} 0 1 *ᵥ
      (fun w => certificateLocalFrame1_4 w c) = 0 := by
    intro c
    apply certificateLocalGenerator_annihilates_of_check
    fin_cases c <;> decide
  ext w c
  exact congrFun (hc c) w

/-- Sector 1, type 4: the literal signed E12 annihilates every column. -/
theorem certificateLocalFrame1_4_raising12 :
    certificateLocalGenerator {0, 1, 2} 1 2 * certificateLocalFrame1_4 = 0 := by
  have hc : ∀ c : Fin 7, certificateLocalGenerator {0, 1, 2} 1 2 *ᵥ
      (fun w => certificateLocalFrame1_4 w c) = 0 := by
    intro c
    apply certificateLocalGenerator_annihilates_of_check
    fin_cases c <;> decide
  ext w c
  exact congrFun (hc c) w

/-- Sector 1, type 5: the declared signed highest weight on physical rows. -/
theorem certificateLocalFrame1_5_weight (w : CertificateLocalWord)
    (c : Fin 7) (i : Fin 3) :
    certificateLocalWeight {0, 1, 2} w i * certificateLocalFrame1_5 w c =
      (![1, 1, -2] : Fin 3 → ℤ) i * certificateLocalFrame1_5 w c := by
  exact certificateLocalFrame_weight_of_check {0, 1, 2} ![1, 1, -2]
    certificateLocalFrameEntries1_5 c (by fin_cases c <;> decide) i w

/-- Sector 1, type 5: the literal signed E01 annihilates every column. -/
theorem certificateLocalFrame1_5_raising01 :
    certificateLocalGenerator {0, 1, 2} 0 1 * certificateLocalFrame1_5 = 0 := by
  have hc : ∀ c : Fin 7, certificateLocalGenerator {0, 1, 2} 0 1 *ᵥ
      (fun w => certificateLocalFrame1_5 w c) = 0 := by
    intro c
    apply certificateLocalGenerator_annihilates_of_check
    fin_cases c <;> decide
  ext w c
  exact congrFun (hc c) w

/-- Sector 1, type 5: the literal signed E12 annihilates every column. -/
theorem certificateLocalFrame1_5_raising12 :
    certificateLocalGenerator {0, 1, 2} 1 2 * certificateLocalFrame1_5 = 0 := by
  have hc : ∀ c : Fin 7, certificateLocalGenerator {0, 1, 2} 1 2 *ᵥ
      (fun w => certificateLocalFrame1_5 w c) = 0 := by
    intro c
    apply certificateLocalGenerator_annihilates_of_check
    fin_cases c <;> decide
  ext w c
  exact congrFun (hc c) w

/-- Sector 1, type 6: the declared signed highest weight on physical rows. -/
theorem certificateLocalFrame1_6_weight (w : CertificateLocalWord)
    (c : Fin 17) (i : Fin 3) :
    certificateLocalWeight {0, 1, 2} w i * certificateLocalFrame1_6 w c =
      (![1, 0, -1] : Fin 3 → ℤ) i * certificateLocalFrame1_6 w c := by
  exact certificateLocalFrame_weight_of_check {0, 1, 2} ![1, 0, -1]
    certificateLocalFrameEntries1_6 c (by fin_cases c <;> decide) i w

/-- Sector 1, type 6: the literal signed E01 annihilates every column. -/
theorem certificateLocalFrame1_6_raising01 :
    certificateLocalGenerator {0, 1, 2} 0 1 * certificateLocalFrame1_6 = 0 := by
  have hc : ∀ c : Fin 17, certificateLocalGenerator {0, 1, 2} 0 1 *ᵥ
      (fun w => certificateLocalFrame1_6 w c) = 0 := by
    intro c
    apply certificateLocalGenerator_annihilates_of_check
    fin_cases c <;> decide
  ext w c
  exact congrFun (hc c) w

/-- Sector 1, type 6: the literal signed E12 annihilates every column. -/
theorem certificateLocalFrame1_6_raising12 :
    certificateLocalGenerator {0, 1, 2} 1 2 * certificateLocalFrame1_6 = 0 := by
  have hc : ∀ c : Fin 17, certificateLocalGenerator {0, 1, 2} 1 2 *ᵥ
      (fun w => certificateLocalFrame1_6 w c) = 0 := by
    intro c
    apply certificateLocalGenerator_annihilates_of_check
    fin_cases c <;> decide
  ext w c
  exact congrFun (hc c) w

/-- Sector 1, type 7: the declared signed highest weight on physical rows. -/
theorem certificateLocalFrame1_7_weight (w : CertificateLocalWord)
    (c : Fin 6) (i : Fin 3) :
    certificateLocalWeight {0, 1, 2} w i * certificateLocalFrame1_7 w c =
      (![0, 0, 0] : Fin 3 → ℤ) i * certificateLocalFrame1_7 w c := by
  exact certificateLocalFrame_weight_of_check {0, 1, 2} ![0, 0, 0]
    certificateLocalFrameEntries1_7 c (by fin_cases c <;> decide) i w

/-- Sector 1, type 7: the literal signed E01 annihilates every column. -/
theorem certificateLocalFrame1_7_raising01 :
    certificateLocalGenerator {0, 1, 2} 0 1 * certificateLocalFrame1_7 = 0 := by
  have hc : ∀ c : Fin 6, certificateLocalGenerator {0, 1, 2} 0 1 *ᵥ
      (fun w => certificateLocalFrame1_7 w c) = 0 := by
    intro c
    apply certificateLocalGenerator_annihilates_of_check
    fin_cases c <;> decide
  ext w c
  exact congrFun (hc c) w

/-- Sector 1, type 7: the literal signed E12 annihilates every column. -/
theorem certificateLocalFrame1_7_raising12 :
    certificateLocalGenerator {0, 1, 2} 1 2 * certificateLocalFrame1_7 = 0 := by
  have hc : ∀ c : Fin 6, certificateLocalGenerator {0, 1, 2} 1 2 *ᵥ
      (fun w => certificateLocalFrame1_7 w c) = 0 := by
    intro c
    apply certificateLocalGenerator_annihilates_of_check
    fin_cases c <;> decide
  ext w c
  exact congrFun (hc c) w

/-- Sector 2, type 0: the declared signed highest weight on physical rows. -/
theorem certificateLocalFrame2_0_weight (w : CertificateLocalWord)
    (c : Fin 1) (i : Fin 3) :
    certificateLocalWeight {0} w i * certificateLocalFrame2_0 w c =
      (![1, 0, -5] : Fin 3 → ℤ) i * certificateLocalFrame2_0 w c := by
  exact certificateLocalFrame_weight_of_check {0} ![1, 0, -5]
    certificateLocalFrameEntries2_0 c (by fin_cases c <;> decide) i w

/-- Sector 2, type 0: the literal signed E01 annihilates every column. -/
theorem certificateLocalFrame2_0_raising01 :
    certificateLocalGenerator {0} 0 1 * certificateLocalFrame2_0 = 0 := by
  have hc : ∀ c : Fin 1, certificateLocalGenerator {0} 0 1 *ᵥ
      (fun w => certificateLocalFrame2_0 w c) = 0 := by
    intro c
    apply certificateLocalGenerator_annihilates_of_check
    fin_cases c <;> decide
  ext w c
  exact congrFun (hc c) w

/-- Sector 2, type 0: the literal signed E12 annihilates every column. -/
theorem certificateLocalFrame2_0_raising12 :
    certificateLocalGenerator {0} 1 2 * certificateLocalFrame2_0 = 0 := by
  have hc : ∀ c : Fin 1, certificateLocalGenerator {0} 1 2 *ᵥ
      (fun w => certificateLocalFrame2_0 w c) = 0 := by
    intro c
    apply certificateLocalGenerator_annihilates_of_check
    fin_cases c <;> decide
  ext w c
  exact congrFun (hc c) w

/-- Sector 2, type 1: the declared signed highest weight on physical rows. -/
theorem certificateLocalFrame2_1_weight (w : CertificateLocalWord)
    (c : Fin 4) (i : Fin 3) :
    certificateLocalWeight {0} w i * certificateLocalFrame2_1 w c =
      (![1, -1, -4] : Fin 3 → ℤ) i * certificateLocalFrame2_1 w c := by
  exact certificateLocalFrame_weight_of_check {0} ![1, -1, -4]
    certificateLocalFrameEntries2_1 c (by fin_cases c <;> decide) i w

/-- Sector 2, type 1: the literal signed E01 annihilates every column. -/
theorem certificateLocalFrame2_1_raising01 :
    certificateLocalGenerator {0} 0 1 * certificateLocalFrame2_1 = 0 := by
  have hc : ∀ c : Fin 4, certificateLocalGenerator {0} 0 1 *ᵥ
      (fun w => certificateLocalFrame2_1 w c) = 0 := by
    intro c
    apply certificateLocalGenerator_annihilates_of_check
    fin_cases c <;> decide
  ext w c
  exact congrFun (hc c) w

/-- Sector 2, type 1: the literal signed E12 annihilates every column. -/
theorem certificateLocalFrame2_1_raising12 :
    certificateLocalGenerator {0} 1 2 * certificateLocalFrame2_1 = 0 := by
  have hc : ∀ c : Fin 4, certificateLocalGenerator {0} 1 2 *ᵥ
      (fun w => certificateLocalFrame2_1 w c) = 0 := by
    intro c
    apply certificateLocalGenerator_annihilates_of_check
    fin_cases c <;> decide
  ext w c
  exact congrFun (hc c) w

/-- Sector 2, type 2: the declared signed highest weight on physical rows. -/
theorem certificateLocalFrame2_2_weight (w : CertificateLocalWord)
    (c : Fin 5) (i : Fin 3) :
    certificateLocalWeight {0} w i * certificateLocalFrame2_2 w c =
      (![0, 0, -4] : Fin 3 → ℤ) i * certificateLocalFrame2_2 w c := by
  exact certificateLocalFrame_weight_of_check {0} ![0, 0, -4]
    certificateLocalFrameEntries2_2 c (by fin_cases c <;> decide) i w

/-- Sector 2, type 2: the literal signed E01 annihilates every column. -/
theorem certificateLocalFrame2_2_raising01 :
    certificateLocalGenerator {0} 0 1 * certificateLocalFrame2_2 = 0 := by
  have hc : ∀ c : Fin 5, certificateLocalGenerator {0} 0 1 *ᵥ
      (fun w => certificateLocalFrame2_2 w c) = 0 := by
    intro c
    apply certificateLocalGenerator_annihilates_of_check
    fin_cases c <;> decide
  ext w c
  exact congrFun (hc c) w

/-- Sector 2, type 2: the literal signed E12 annihilates every column. -/
theorem certificateLocalFrame2_2_raising12 :
    certificateLocalGenerator {0} 1 2 * certificateLocalFrame2_2 = 0 := by
  have hc : ∀ c : Fin 5, certificateLocalGenerator {0} 1 2 *ᵥ
      (fun w => certificateLocalFrame2_2 w c) = 0 := by
    intro c
    apply certificateLocalGenerator_annihilates_of_check
    fin_cases c <;> decide
  ext w c
  exact congrFun (hc c) w

/-- Sector 2, type 3: the declared signed highest weight on physical rows. -/
theorem certificateLocalFrame2_3_weight (w : CertificateLocalWord)
    (c : Fin 5) (i : Fin 3) :
    certificateLocalWeight {0} w i * certificateLocalFrame2_3 w c =
      (![1, -2, -3] : Fin 3 → ℤ) i * certificateLocalFrame2_3 w c := by
  exact certificateLocalFrame_weight_of_check {0} ![1, -2, -3]
    certificateLocalFrameEntries2_3 c (by fin_cases c <;> decide) i w

/-- Sector 2, type 3: the literal signed E01 annihilates every column. -/
theorem certificateLocalFrame2_3_raising01 :
    certificateLocalGenerator {0} 0 1 * certificateLocalFrame2_3 = 0 := by
  have hc : ∀ c : Fin 5, certificateLocalGenerator {0} 0 1 *ᵥ
      (fun w => certificateLocalFrame2_3 w c) = 0 := by
    intro c
    apply certificateLocalGenerator_annihilates_of_check
    fin_cases c <;> decide
  ext w c
  exact congrFun (hc c) w

/-- Sector 2, type 3: the literal signed E12 annihilates every column. -/
theorem certificateLocalFrame2_3_raising12 :
    certificateLocalGenerator {0} 1 2 * certificateLocalFrame2_3 = 0 := by
  have hc : ∀ c : Fin 5, certificateLocalGenerator {0} 1 2 *ᵥ
      (fun w => certificateLocalFrame2_3 w c) = 0 := by
    intro c
    apply certificateLocalGenerator_annihilates_of_check
    fin_cases c <;> decide
  ext w c
  exact congrFun (hc c) w

/-- Sector 2, type 4: the declared signed highest weight on physical rows. -/
theorem certificateLocalFrame2_4_weight (w : CertificateLocalWord)
    (c : Fin 15) (i : Fin 3) :
    certificateLocalWeight {0} w i * certificateLocalFrame2_4 w c =
      (![0, -1, -3] : Fin 3 → ℤ) i * certificateLocalFrame2_4 w c := by
  exact certificateLocalFrame_weight_of_check {0} ![0, -1, -3]
    certificateLocalFrameEntries2_4 c (by fin_cases c <;> decide) i w

/-- Sector 2, type 4: the literal signed E01 annihilates every column. -/
theorem certificateLocalFrame2_4_raising01 :
    certificateLocalGenerator {0} 0 1 * certificateLocalFrame2_4 = 0 := by
  have hc : ∀ c : Fin 15, certificateLocalGenerator {0} 0 1 *ᵥ
      (fun w => certificateLocalFrame2_4 w c) = 0 := by
    intro c
    apply certificateLocalGenerator_annihilates_of_check
    fin_cases c <;> decide
  ext w c
  exact congrFun (hc c) w

/-- Sector 2, type 4: the literal signed E12 annihilates every column. -/
theorem certificateLocalFrame2_4_raising12 :
    certificateLocalGenerator {0} 1 2 * certificateLocalFrame2_4 = 0 := by
  have hc : ∀ c : Fin 15, certificateLocalGenerator {0} 1 2 *ᵥ
      (fun w => certificateLocalFrame2_4 w c) = 0 := by
    intro c
    apply certificateLocalGenerator_annihilates_of_check
    fin_cases c <;> decide
  ext w c
  exact congrFun (hc c) w

/-- Sector 2, type 5: the declared signed highest weight on physical rows. -/
theorem certificateLocalFrame2_5_weight (w : CertificateLocalWord)
    (c : Fin 10) (i : Fin 3) :
    certificateLocalWeight {0} w i * certificateLocalFrame2_5 w c =
      (![0, -2, -2] : Fin 3 → ℤ) i * certificateLocalFrame2_5 w c := by
  exact certificateLocalFrame_weight_of_check {0} ![0, -2, -2]
    certificateLocalFrameEntries2_5 c (by fin_cases c <;> decide) i w

/-- Sector 2, type 5: the literal signed E01 annihilates every column. -/
theorem certificateLocalFrame2_5_raising01 :
    certificateLocalGenerator {0} 0 1 * certificateLocalFrame2_5 = 0 := by
  have hc : ∀ c : Fin 10, certificateLocalGenerator {0} 0 1 *ᵥ
      (fun w => certificateLocalFrame2_5 w c) = 0 := by
    intro c
    apply certificateLocalGenerator_annihilates_of_check
    fin_cases c <;> decide
  ext w c
  exact congrFun (hc c) w

/-- Sector 2, type 5: the literal signed E12 annihilates every column. -/
theorem certificateLocalFrame2_5_raising12 :
    certificateLocalGenerator {0} 1 2 * certificateLocalFrame2_5 = 0 := by
  have hc : ∀ c : Fin 10, certificateLocalGenerator {0} 1 2 *ᵥ
      (fun w => certificateLocalFrame2_5 w c) = 0 := by
    intro c
    apply certificateLocalGenerator_annihilates_of_check
    fin_cases c <;> decide
  ext w c
  exact congrFun (hc c) w

/-- Sector 2, type 6: the declared signed highest weight on physical rows. -/
theorem certificateLocalFrame2_6_weight (w : CertificateLocalWord)
    (c : Fin 11) (i : Fin 3) :
    certificateLocalWeight {0} w i * certificateLocalFrame2_6 w c =
      (![-1, -1, -2] : Fin 3 → ℤ) i * certificateLocalFrame2_6 w c := by
  exact certificateLocalFrame_weight_of_check {0} ![-1, -1, -2]
    certificateLocalFrameEntries2_6 c (by fin_cases c <;> decide) i w

/-- Sector 2, type 6: the literal signed E01 annihilates every column. -/
theorem certificateLocalFrame2_6_raising01 :
    certificateLocalGenerator {0} 0 1 * certificateLocalFrame2_6 = 0 := by
  have hc : ∀ c : Fin 11, certificateLocalGenerator {0} 0 1 *ᵥ
      (fun w => certificateLocalFrame2_6 w c) = 0 := by
    intro c
    apply certificateLocalGenerator_annihilates_of_check
    fin_cases c <;> decide
  ext w c
  exact congrFun (hc c) w

/-- Sector 2, type 6: the literal signed E12 annihilates every column. -/
theorem certificateLocalFrame2_6_raising12 :
    certificateLocalGenerator {0} 1 2 * certificateLocalFrame2_6 = 0 := by
  have hc : ∀ c : Fin 11, certificateLocalGenerator {0} 1 2 *ᵥ
      (fun w => certificateLocalFrame2_6 w c) = 0 := by
    intro c
    apply certificateLocalGenerator_annihilates_of_check
    fin_cases c <;> decide
  ext w c
  exact congrFun (hc c) w

end ThreeCopyQutritWerner
