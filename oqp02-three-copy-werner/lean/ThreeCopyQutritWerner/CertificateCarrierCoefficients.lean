module

public import ThreeCopyQutritWerner.CertificateCarrierPermutations
public import ThreeCopyQutritWerner.CertificateS3Projections
public import ThreeCopyQutritWerner.CertificatePermutationTables
public import ThreeCopyQutritWerner.CertificateCharacter

@[expose] public section


/-!
Exact original carrier weights in canonical character/antisymmetrizer form.
The source's permutation order is retained and bound to complete S5/S4 and
S3-times-two enumerations. These are coefficient identities; the physical
matrix interpretation is a separate assembly step.
-/

noncomputable section

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace ThreeCopyQutritWerner

def certificateCarrierIndex0 : Fin 120 → Fin 120 :=
  ![0, 1, 6, 7, 2, 4, 8, 10, 5, 3, 11, 9, 12, 18, 14, 20, 16, 22, 17, 23, 19, 13, 21, 15, 24, 25, 48, 49, 26, 28, 50, 52, 27, 29, 51, 53, 30, 31, 54, 55, 36, 42, 60, 66, 39, 45, 63, 69, 40, 46, 64, 70, 43, 37, 67, 61, 44, 38, 68, 62, 47, 41, 71, 65, 57, 59, 33, 35, 58, 56, 34, 32, 75, 99, 73, 97, 76, 100, 77, 101, 79, 103, 85, 109, 81, 105, 87, 111, 83, 107, 89, 113, 91, 115, 90, 114, 95, 119, 93, 117, 98, 74, 96, 72, 102, 78, 108, 84, 104, 80, 110, 86, 106, 82, 112, 88, 118, 94, 116, 92]

def certificateCarrierIndex0Swap12 : Fin 120 → Fin 120 :=
  ![6, 7, 0, 1, 12, 18, 14, 20, 19, 13, 21, 15, 2, 4, 8, 10, 22, 16, 23, 17, 5, 3, 11, 9, 30, 31, 54, 55, 36, 42, 60, 66, 37, 43, 61, 67, 24, 25, 48, 49, 26, 28, 50, 52, 33, 35, 57, 59, 46, 40, 70, 64, 29, 27, 53, 51, 34, 32, 58, 56, 41, 47, 65, 71, 63, 69, 39, 45, 68, 62, 44, 38, 85, 109, 79, 103, 90, 114, 91, 115, 73, 97, 75, 99, 87, 111, 81, 105, 93, 117, 95, 119, 77, 101, 76, 100, 89, 113, 83, 107, 108, 84, 102, 78, 96, 72, 98, 74, 110, 86, 104, 80, 116, 92, 118, 94, 112, 88, 106, 82]

def certificateCarrierIndex0Swap34 : Fin 120 → Fin 120 :=
  ![1, 0, 7, 6, 3, 5, 9, 11, 4, 2, 10, 8, 13, 19, 15, 21, 17, 23, 16, 22, 18, 12, 20, 14, 25, 24, 49, 48, 27, 29, 51, 53, 26, 28, 50, 52, 31, 30, 55, 54, 37, 43, 61, 67, 38, 44, 62, 68, 41, 47, 65, 71, 42, 36, 66, 60, 45, 39, 69, 63, 46, 40, 70, 64, 56, 58, 32, 34, 59, 57, 35, 33, 74, 98, 72, 96, 77, 101, 76, 100, 78, 102, 84, 108, 80, 104, 86, 110, 82, 106, 88, 112, 90, 114, 91, 115, 94, 118, 92, 116, 99, 75, 97, 73, 103, 79, 109, 85, 105, 81, 111, 87, 107, 83, 113, 89, 119, 95, 117, 93]

def certificateCarrierIndex0SwapBoth : Fin 120 → Fin 120 :=
  ![7, 6, 1, 0, 13, 19, 15, 21, 18, 12, 20, 14, 3, 5, 9, 11, 23, 17, 22, 16, 4, 2, 10, 8, 31, 30, 55, 54, 37, 43, 61, 67, 36, 42, 60, 66, 25, 24, 49, 48, 27, 29, 51, 53, 32, 34, 56, 58, 47, 41, 71, 65, 28, 26, 52, 50, 35, 33, 59, 57, 40, 46, 64, 70, 62, 68, 38, 44, 69, 63, 45, 39, 84, 108, 78, 102, 91, 115, 90, 114, 72, 96, 74, 98, 86, 110, 80, 104, 92, 116, 94, 118, 76, 100, 77, 101, 88, 112, 82, 106, 109, 85, 103, 79, 97, 73, 99, 75, 111, 87, 105, 81, 117, 93, 119, 95, 113, 89, 107, 83]

theorem certificateCarrierIndex0_bijective : Function.Bijective certificateCarrierIndex0 := by decide

theorem certificateCarrierPerm0_restrict (p : Fin 120) (i : Fin 5) :
    certificateCarrierPerm0 p i.castSucc = (certificatePerm5 (certificateCarrierIndex0 p) i).castSucc := by
  fin_cases p <;> fin_cases i <;> decide

theorem certificateCarrierPerm0_last (p : Fin 120) : certificateCarrierPerm0 p 5 = 5 := by
  fin_cases p <;> decide

theorem certificateCarrierIndex0_Swap12 (p : Fin 120) :
    certificatePerm5 (certificateCarrierIndex0 p) * Equiv.swap 1 2 = certificatePerm5 (certificateCarrierIndex0Swap12 p) := by
  fin_cases p <;> decide

theorem certificateCarrierIndex0_Swap34 (p : Fin 120) :
    certificatePerm5 (certificateCarrierIndex0 p) * Equiv.swap 3 4 = certificatePerm5 (certificateCarrierIndex0Swap34 p) := by
  fin_cases p <;> decide

theorem certificateCarrierIndex0_SwapBoth (p : Fin 120) :
    certificatePerm5 (certificateCarrierIndex0 p) * Equiv.swap 1 2 * Equiv.swap 3 4 = certificatePerm5 (certificateCarrierIndex0SwapBoth p) := by
  fin_cases p <;> decide

theorem certificateCarrierWeight0_character (p : Fin 120) :
    certificateCarrierWeight0 p =
      (certificateCharacter (certificatePerm5 (certificateCarrierIndex0 p)) -
        certificateCharacter (certificatePerm5 (certificateCarrierIndex0 p) * Equiv.swap 1 2) -
        certificateCharacter (certificatePerm5 (certificateCarrierIndex0 p) * Equiv.swap 3 4) +
        certificateCharacter (certificatePerm5 (certificateCarrierIndex0 p) * Equiv.swap 1 2 * Equiv.swap 3 4)) /
          (4 * 24) := by
  rw [certificateCarrierIndex0_SwapBoth, certificateCarrierIndex0_Swap12,
    certificateCarrierIndex0_Swap34]
  simp only [certificateCharacter_perm5]
  fin_cases p <;> norm_num [certificateCarrierWeight0, certificateCarrierNumerator0,
    certificateCarrierDenominator0, certificateCarrierIndex0,
    certificateCarrierIndex0Swap12, certificateCarrierIndex0Swap34,
    certificateCarrierIndex0SwapBoth, certificateCharacterTable5]

def certificateCarrierIndex2 : Fin 24 → Fin 24 :=
  ![0, 1, 6, 7, 3, 5, 9, 11, 4, 2, 10, 8, 12, 18, 14, 20, 15, 21, 13, 19, 16, 22, 17, 23]

def certificateCarrierIndex2Swap12 : Fin 24 → Fin 24 :=
  ![6, 7, 0, 1, 13, 19, 15, 21, 18, 12, 20, 14, 2, 4, 8, 10, 9, 11, 3, 5, 22, 16, 23, 17]

def certificateCarrierIndex2Swap34 : Fin 24 → Fin 24 :=
  ![1, 0, 7, 6, 2, 4, 8, 10, 5, 3, 11, 9, 13, 19, 15, 21, 14, 20, 12, 18, 17, 23, 16, 22]

def certificateCarrierIndex2SwapBoth : Fin 24 → Fin 24 :=
  ![7, 6, 1, 0, 12, 18, 14, 20, 19, 13, 21, 15, 3, 5, 9, 11, 8, 10, 2, 4, 23, 17, 22, 16]

theorem certificateCarrierIndex2_bijective : Function.Bijective certificateCarrierIndex2 := by decide

theorem certificateCarrierPerm2_restrict (p : Fin 24) (i : Fin 4) :
    certificateCarrierPerm2 p i.succ.castSucc =
      (certificatePerm4 (certificateCarrierIndex2 p) i).succ.castSucc := by
  fin_cases p <;> fin_cases i <;> decide

theorem certificateCarrierPerm2_endpoints (p : Fin 24) :
    certificateCarrierPerm2 p 0 = 0 ∧ certificateCarrierPerm2 p 5 = 5 := by
  fin_cases p <;> decide

theorem certificateCarrierIndex2_Swap12 (p : Fin 24) :
    certificatePerm4 (certificateCarrierIndex2 p) * Equiv.swap 0 1 = certificatePerm4 (certificateCarrierIndex2Swap12 p) := by
  fin_cases p <;> decide

theorem certificateCarrierIndex2_Swap34 (p : Fin 24) :
    certificatePerm4 (certificateCarrierIndex2 p) * Equiv.swap 2 3 = certificatePerm4 (certificateCarrierIndex2Swap34 p) := by
  fin_cases p <;> decide

theorem certificateCarrierIndex2_SwapBoth (p : Fin 24) :
    certificatePerm4 (certificateCarrierIndex2 p) * Equiv.swap 0 1 * Equiv.swap 2 3 = certificatePerm4 (certificateCarrierIndex2SwapBoth p) := by
  fin_cases p <;> decide

theorem certificateCarrierWeight2_character (p : Fin 24) :
    certificateCarrierWeight2 p =
      (certificateCharacter (certificatePerm4 (certificateCarrierIndex2 p)) -
        certificateCharacter (certificatePerm4 (certificateCarrierIndex2 p) * Equiv.swap 0 1) -
        certificateCharacter (certificatePerm4 (certificateCarrierIndex2 p) * Equiv.swap 2 3) +
        certificateCharacter (certificatePerm4 (certificateCarrierIndex2 p) * Equiv.swap 0 1 * Equiv.swap 2 3)) /
          (4 * 12) := by
  rw [certificateCarrierIndex2_SwapBoth, certificateCarrierIndex2_Swap12,
    certificateCarrierIndex2_Swap34]
  simp only [certificateCharacter_perm4]
  fin_cases p <;> norm_num [certificateCarrierWeight2, certificateCarrierNumerator2,
    certificateCarrierDenominator2, certificateCarrierIndex2,
    certificateCarrierIndex2Swap12, certificateCarrierIndex2Swap34,
    certificateCarrierIndex2SwapBoth, certificateCharacterTable4]

def certificateCarrierIndex1 : Fin 12 → Fin 6 × Fin 2 :=
  ![(1, 0), (1, 1), (2, 0), (2, 1), (3, 0), (3, 1), (5, 0), (5, 1), (0, 0), (0, 1), (4, 0), (4, 1)]

theorem certificateCarrierIndex1_bijective : Function.Bijective certificateCarrierIndex1 := by decide

theorem certificateCarrierPerm1_first (p : Fin 12) (i : Fin 3) :
    certificateCarrierPerm1 p (i.castLE (by decide)) =
      (certificatePerm3 (certificateCarrierIndex1 p).1 i).castLE (by decide) := by
  fin_cases p <;> fin_cases i <;> decide

theorem certificateCarrierPerm1_last (p : Fin 12) : certificateCarrierPerm1 p 5 = 5 := by
  fin_cases p <;> decide

theorem certificateCarrierPerm1_minor (p : Fin 12) :
    certificateCarrierPerm1 p 3 = (if (certificateCarrierIndex1 p).2 = 0 then 3 else 4) ∧
    certificateCarrierPerm1 p 4 = (if (certificateCarrierIndex1 p).2 = 0 then 4 else 3) := by
  fin_cases p <;> decide

/-- The mixed carrier is (A12 minus the three-register alternator) times A34. -/
theorem certificateCarrierWeight1_antisym (p : Fin 12) :
    certificateCarrierWeight1 p =
      ((if certificatePerm3 (certificateCarrierIndex1 p).1 = 1 then (1 / 2 : ℚ) else 0) -
       (if certificatePerm3 (certificateCarrierIndex1 p).1 = Equiv.swap 1 2 then (1 / 2 : ℚ) else 0) -
       certificateS3Weight 1 (certificatePerm3 (certificateCarrierIndex1 p).1)) *
      (if (certificateCarrierIndex1 p).2 = 0 then (1 / 2 : ℚ) else -(1 / 2 : ℚ)) := by
  fin_cases p <;> decide +kernel

end ThreeCopyQutritWerner
