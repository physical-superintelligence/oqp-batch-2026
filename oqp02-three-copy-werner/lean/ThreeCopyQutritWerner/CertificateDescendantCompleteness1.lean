module

public import ThreeCopyQutritWerner.CertificateDescendantBlockChecks1

@[expose] public section


/-!
Exact sector-1 physical completeness from 33 finite integer inverse checks.
The columns here are the literal sparse descendant candidates; their separate
lowering-program theorem binds them to the original archive highest frames.
-/

noncomputable section

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

abbrev CertificateDescendantIndex1 := Σ b : Fin 37, Fin (certificateDescendantSizes1 b)

def certificateDescendantRow1 (r : CertificateDescendantIndex1) : CertificateLocalWord :=
  certificateDescendantBlockRows1 r.1 r.2

def certificateDescendantPhysical1 : Matrix CertificateLocalWord CertificateDescendantIndex1 ℤ :=
  fun w c => certificateSparseVector
    (certificateDescendantColumns1 (certificateDescendantBlockColumns1 c.1 c.2)) w

def certificateDescendantMatrices1 : ∀ b : Fin 37,
    Matrix (Fin (certificateDescendantSizes1 b)) (Fin (certificateDescendantSizes1 b)) ℤ := by
  exact
    Fin.cases (certificateDescendantBlockA1_00) <|
    Fin.cases (certificateDescendantBlockA1_01) <|
    Fin.cases (certificateDescendantBlockA1_02) <|
    Fin.cases (certificateDescendantBlockA1_03) <|
    Fin.cases (certificateDescendantBlockA1_04) <|
    Fin.cases (certificateDescendantBlockA1_05) <|
    Fin.cases (certificateDescendantBlockA1_06) <|
    Fin.cases (certificateDescendantBlockA1_07) <|
    Fin.cases (certificateDescendantBlockA1_08) <|
    Fin.cases (certificateDescendantBlockA1_09) <|
    Fin.cases (certificateDescendantBlockA1_10) <|
    Fin.cases (certificateDescendantBlockA1_11) <|
    Fin.cases (certificateDescendantBlockA1_12) <|
    Fin.cases (certificateDescendantBlockA1_13) <|
    Fin.cases (certificateDescendantBlockA1_14) <|
    Fin.cases (certificateDescendantBlockA1_15) <|
    Fin.cases (certificateDescendantBlockA1_16) <|
    Fin.cases (certificateDescendantBlockA1_17) <|
    Fin.cases (certificateDescendantBlockA1_18) <|
    Fin.cases (certificateDescendantBlockA1_19) <|
    Fin.cases (certificateDescendantBlockA1_20) <|
    Fin.cases (certificateDescendantBlockA1_21) <|
    Fin.cases (certificateDescendantBlockA1_22) <|
    Fin.cases (certificateDescendantBlockA1_23) <|
    Fin.cases (certificateDescendantBlockA1_24) <|
    Fin.cases (certificateDescendantBlockA1_25) <|
    Fin.cases (certificateDescendantBlockA1_26) <|
    Fin.cases (certificateDescendantBlockA1_27) <|
    Fin.cases (certificateDescendantBlockA1_28) <|
    Fin.cases (certificateDescendantBlockA1_29) <|
    Fin.cases (certificateDescendantBlockA1_30) <|
    Fin.cases (certificateDescendantBlockA1_31) <|
    Fin.cases (certificateDescendantBlockA1_32) <|
    Fin.cases (certificateDescendantBlockA1_33) <|
    Fin.cases (certificateDescendantBlockA1_34) <|
    Fin.cases (certificateDescendantBlockA1_35) <|
    Fin.cases (certificateDescendantBlockA1_36) <|
    Fin.rec0

def certificateDescendantInverse1 : ∀ b : Fin 37,
    Matrix (Fin (certificateDescendantSizes1 b)) (Fin (certificateDescendantSizes1 b)) ℚ := by
  exact
    Fin.cases ((216 : ℚ)⁻¹ • (certificateDescendantBlockW1_00.map (Int.cast : ℤ → ℚ))) <|
    Fin.cases ((216 : ℚ)⁻¹ • (certificateDescendantBlockW1_01.map (Int.cast : ℤ → ℚ))) <|
    Fin.cases ((216 : ℚ)⁻¹ • (certificateDescendantBlockW1_02.map (Int.cast : ℤ → ℚ))) <|
    Fin.cases ((36 : ℚ)⁻¹ • (certificateDescendantBlockW1_03.map (Int.cast : ℤ → ℚ))) <|
    Fin.cases ((1728 : ℚ)⁻¹ • (certificateDescendantBlockW1_04.map (Int.cast : ℤ → ℚ))) <|
    Fin.cases ((12096 : ℚ)⁻¹ • (certificateDescendantBlockW1_05.map (Int.cast : ℤ → ℚ))) <|
    Fin.cases ((6048 : ℚ)⁻¹ • (certificateDescendantBlockW1_06.map (Int.cast : ℤ → ℚ))) <|
    Fin.cases ((2016 : ℚ)⁻¹ • (certificateDescendantBlockW1_07.map (Int.cast : ℤ → ℚ))) <|
    Fin.cases ((72 : ℚ)⁻¹ • (certificateDescendantBlockW1_08.map (Int.cast : ℤ → ℚ))) <|
    Fin.cases ((8640 : ℚ)⁻¹ • (certificateDescendantBlockW1_09.map (Int.cast : ℤ → ℚ))) <|
    Fin.cases ((36288 : ℚ)⁻¹ • (certificateDescendantBlockW1_10.map (Int.cast : ℤ → ℚ))) <|
    Fin.cases ((90720 : ℚ)⁻¹ • (certificateDescendantBlockW1_11.map (Int.cast : ℤ → ℚ))) <|
    Fin.cases ((90720 : ℚ)⁻¹ • (certificateDescendantBlockW1_12.map (Int.cast : ℤ → ℚ))) <|
    Fin.cases ((3024 : ℚ)⁻¹ • (certificateDescendantBlockW1_13.map (Int.cast : ℤ → ℚ))) <|
    Fin.cases ((72 : ℚ)⁻¹ • (certificateDescendantBlockW1_14.map (Int.cast : ℤ → ℚ))) <|
    Fin.cases ((4320 : ℚ)⁻¹ • (certificateDescendantBlockW1_15.map (Int.cast : ℤ → ℚ))) <|
    Fin.cases ((60480 : ℚ)⁻¹ • (certificateDescendantBlockW1_16.map (Int.cast : ℤ → ℚ))) <|
    Fin.cases ((30240 : ℚ)⁻¹ • (certificateDescendantBlockW1_17.map (Int.cast : ℤ → ℚ))) <|
    Fin.cases ((15120 : ℚ)⁻¹ • (certificateDescendantBlockW1_18.map (Int.cast : ℤ → ℚ))) <|
    Fin.cases ((15120 : ℚ)⁻¹ • (certificateDescendantBlockW1_19.map (Int.cast : ℤ → ℚ))) <|
    Fin.cases ((504 : ℚ)⁻¹ • (certificateDescendantBlockW1_20.map (Int.cast : ℤ → ℚ))) <|
    Fin.cases ((6 : ℚ)⁻¹ • (certificateDescendantBlockW1_21.map (Int.cast : ℤ → ℚ))) <|
    Fin.cases ((720 : ℚ)⁻¹ • (certificateDescendantBlockW1_22.map (Int.cast : ℤ → ℚ))) <|
    Fin.cases ((3024 : ℚ)⁻¹ • (certificateDescendantBlockW1_23.map (Int.cast : ℤ → ℚ))) <|
    Fin.cases ((15120 : ℚ)⁻¹ • (certificateDescendantBlockW1_24.map (Int.cast : ℤ → ℚ))) <|
    Fin.cases ((7560 : ℚ)⁻¹ • (certificateDescendantBlockW1_25.map (Int.cast : ℤ → ℚ))) <|
    Fin.cases ((504 : ℚ)⁻¹ • (certificateDescendantBlockW1_26.map (Int.cast : ℤ → ℚ))) <|
    Fin.cases ((6 : ℚ)⁻¹ • (certificateDescendantBlockW1_27.map (Int.cast : ℤ → ℚ))) <|
    Fin.cases ((72 : ℚ)⁻¹ • (certificateDescendantBlockW1_28.map (Int.cast : ℤ → ℚ))) <|
    Fin.cases ((504 : ℚ)⁻¹ • (certificateDescendantBlockW1_29.map (Int.cast : ℤ → ℚ))) <|
    Fin.cases ((504 : ℚ)⁻¹ • (certificateDescendantBlockW1_30.map (Int.cast : ℤ → ℚ))) <|
    Fin.cases ((84 : ℚ)⁻¹ • (certificateDescendantBlockW1_31.map (Int.cast : ℤ → ℚ))) <|
    Fin.cases ((3 : ℚ)⁻¹ • (certificateDescendantBlockW1_32.map (Int.cast : ℤ → ℚ))) <|
    Fin.cases ((6 : ℚ)⁻¹ • (certificateDescendantBlockW1_33.map (Int.cast : ℤ → ℚ))) <|
    Fin.cases ((6 : ℚ)⁻¹ • (certificateDescendantBlockW1_34.map (Int.cast : ℤ → ℚ))) <|
    Fin.cases ((3 : ℚ)⁻¹ • (certificateDescendantBlockW1_35.map (Int.cast : ℤ → ℚ))) <|
    Fin.cases ((1 : ℚ)⁻¹ • (certificateDescendantBlockW1_36.map (Int.cast : ℤ → ℚ))) <|
    Fin.rec0

theorem certificateDescendantWeights1_injective :
    Function.Injective certificateDescendantWeights1 := by decide

theorem certificateDescendantBlockRows1_injective (b : Fin 37) :
    Function.Injective (certificateDescendantBlockRows1 b) := by
  fin_cases b
  · exact certificateDescendantBlock1_00_rows_injective
  · exact certificateDescendantBlock1_01_rows_injective
  · exact certificateDescendantBlock1_02_rows_injective
  · exact certificateDescendantBlock1_03_rows_injective
  · exact certificateDescendantBlock1_04_rows_injective
  · exact certificateDescendantBlock1_05_rows_injective
  · exact certificateDescendantBlock1_06_rows_injective
  · exact certificateDescendantBlock1_07_rows_injective
  · exact certificateDescendantBlock1_08_rows_injective
  · exact certificateDescendantBlock1_09_rows_injective
  · exact certificateDescendantBlock1_10_rows_injective
  · exact certificateDescendantBlock1_11_rows_injective
  · exact certificateDescendantBlock1_12_rows_injective
  · exact certificateDescendantBlock1_13_rows_injective
  · exact certificateDescendantBlock1_14_rows_injective
  · exact certificateDescendantBlock1_15_rows_injective
  · exact certificateDescendantBlock1_16_rows_injective
  · exact certificateDescendantBlock1_17_rows_injective
  · exact certificateDescendantBlock1_18_rows_injective
  · exact certificateDescendantBlock1_19_rows_injective
  · exact certificateDescendantBlock1_20_rows_injective
  · exact certificateDescendantBlock1_21_rows_injective
  · exact certificateDescendantBlock1_22_rows_injective
  · exact certificateDescendantBlock1_23_rows_injective
  · exact certificateDescendantBlock1_24_rows_injective
  · exact certificateDescendantBlock1_25_rows_injective
  · exact certificateDescendantBlock1_26_rows_injective
  · exact certificateDescendantBlock1_27_rows_injective
  · exact certificateDescendantBlock1_28_rows_injective
  · exact certificateDescendantBlock1_29_rows_injective
  · exact certificateDescendantBlock1_30_rows_injective
  · exact certificateDescendantBlock1_31_rows_injective
  · exact certificateDescendantBlock1_32_rows_injective
  · exact certificateDescendantBlock1_33_rows_injective
  · exact certificateDescendantBlock1_34_rows_injective
  · exact certificateDescendantBlock1_35_rows_injective
  · exact certificateDescendantBlock1_36_rows_injective

theorem certificateDescendantBlockRows1_weight (b : Fin 37)
    (i : Fin (certificateDescendantSizes1 b)) :
    (fun r => certificateLocalWeight {0, 1, 2} (certificateDescendantBlockRows1 b i) r) =
      certificateDescendantWeights1 b := by
  fin_cases b
  · exact certificateDescendantBlock1_00_row_weight i
  · exact certificateDescendantBlock1_01_row_weight i
  · exact certificateDescendantBlock1_02_row_weight i
  · exact certificateDescendantBlock1_03_row_weight i
  · exact certificateDescendantBlock1_04_row_weight i
  · exact certificateDescendantBlock1_05_row_weight i
  · exact certificateDescendantBlock1_06_row_weight i
  · exact certificateDescendantBlock1_07_row_weight i
  · exact certificateDescendantBlock1_08_row_weight i
  · exact certificateDescendantBlock1_09_row_weight i
  · exact certificateDescendantBlock1_10_row_weight i
  · exact certificateDescendantBlock1_11_row_weight i
  · exact certificateDescendantBlock1_12_row_weight i
  · exact certificateDescendantBlock1_13_row_weight i
  · exact certificateDescendantBlock1_14_row_weight i
  · exact certificateDescendantBlock1_15_row_weight i
  · exact certificateDescendantBlock1_16_row_weight i
  · exact certificateDescendantBlock1_17_row_weight i
  · exact certificateDescendantBlock1_18_row_weight i
  · exact certificateDescendantBlock1_19_row_weight i
  · exact certificateDescendantBlock1_20_row_weight i
  · exact certificateDescendantBlock1_21_row_weight i
  · exact certificateDescendantBlock1_22_row_weight i
  · exact certificateDescendantBlock1_23_row_weight i
  · exact certificateDescendantBlock1_24_row_weight i
  · exact certificateDescendantBlock1_25_row_weight i
  · exact certificateDescendantBlock1_26_row_weight i
  · exact certificateDescendantBlock1_27_row_weight i
  · exact certificateDescendantBlock1_28_row_weight i
  · exact certificateDescendantBlock1_29_row_weight i
  · exact certificateDescendantBlock1_30_row_weight i
  · exact certificateDescendantBlock1_31_row_weight i
  · exact certificateDescendantBlock1_32_row_weight i
  · exact certificateDescendantBlock1_33_row_weight i
  · exact certificateDescendantBlock1_34_row_weight i
  · exact certificateDescendantBlock1_35_row_weight i
  · exact certificateDescendantBlock1_36_row_weight i

theorem certificateDescendantBlockColumns1_weight (b : Fin 37)
    (j : Fin (certificateDescendantSizes1 b)) :
    List.Forall (fun a => (fun r => certificateLocalWeight {0, 1, 2} a.1 r) =
      certificateDescendantWeights1 b)
      (certificateDescendantColumns1 (certificateDescendantBlockColumns1 b j)) := by
  fin_cases b
  · exact certificateDescendantBlock1_00_column_weight j
  · exact certificateDescendantBlock1_01_column_weight j
  · exact certificateDescendantBlock1_02_column_weight j
  · exact certificateDescendantBlock1_03_column_weight j
  · exact certificateDescendantBlock1_04_column_weight j
  · exact certificateDescendantBlock1_05_column_weight j
  · exact certificateDescendantBlock1_06_column_weight j
  · exact certificateDescendantBlock1_07_column_weight j
  · exact certificateDescendantBlock1_08_column_weight j
  · exact certificateDescendantBlock1_09_column_weight j
  · exact certificateDescendantBlock1_10_column_weight j
  · exact certificateDescendantBlock1_11_column_weight j
  · exact certificateDescendantBlock1_12_column_weight j
  · exact certificateDescendantBlock1_13_column_weight j
  · exact certificateDescendantBlock1_14_column_weight j
  · exact certificateDescendantBlock1_15_column_weight j
  · exact certificateDescendantBlock1_16_column_weight j
  · exact certificateDescendantBlock1_17_column_weight j
  · exact certificateDescendantBlock1_18_column_weight j
  · exact certificateDescendantBlock1_19_column_weight j
  · exact certificateDescendantBlock1_20_column_weight j
  · exact certificateDescendantBlock1_21_column_weight j
  · exact certificateDescendantBlock1_22_column_weight j
  · exact certificateDescendantBlock1_23_column_weight j
  · exact certificateDescendantBlock1_24_column_weight j
  · exact certificateDescendantBlock1_25_column_weight j
  · exact certificateDescendantBlock1_26_column_weight j
  · exact certificateDescendantBlock1_27_column_weight j
  · exact certificateDescendantBlock1_28_column_weight j
  · exact certificateDescendantBlock1_29_column_weight j
  · exact certificateDescendantBlock1_30_column_weight j
  · exact certificateDescendantBlock1_31_column_weight j
  · exact certificateDescendantBlock1_32_column_weight j
  · exact certificateDescendantBlock1_33_column_weight j
  · exact certificateDescendantBlock1_34_column_weight j
  · exact certificateDescendantBlock1_35_column_weight j
  · exact certificateDescendantBlock1_36_column_weight j

/-- All 729 physical words occur exactly once in the literal weight rows. -/
theorem certificateDescendantRow1_bijective : Function.Bijective certificateDescendantRow1 := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · exact certificateWeightRows_injective certificateDescendantSizes1
      certificateDescendantBlockRows1 (fun w => fun r => certificateLocalWeight {0, 1, 2} w r)
      certificateDescendantWeights1 certificateDescendantWeights1_injective
      certificateDescendantBlockRows1_injective certificateDescendantBlockRows1_weight
  · norm_num [CertificateDescendantIndex1, CertificateLocalWord, Fintype.card_sigma,
      Fintype.card_fun, certificateDescendantSizes1, Fin.sum_univ_succ]

theorem certificateDescendantPhysical1_blocks :
    certificateDescendantPhysical1.submatrix certificateDescendantRow1 id =
      Matrix.blockDiagonal' certificateDescendantMatrices1 := by
  apply certificateSparseWeightBlocks_diagonal certificateDescendantSizes1
    certificateDescendantBlockRows1
    (fun b j => certificateDescendantColumns1 (certificateDescendantBlockColumns1 b j))
    (fun w => fun r => certificateLocalWeight {0, 1, 2} w r) certificateDescendantWeights1
    certificateDescendantWeights1_injective certificateDescendantMatrices1
    certificateDescendantBlockRows1_weight certificateDescendantBlockColumns1_weight
  intro b i j
  fin_cases b
  · exact certificateDescendantBlock1_00_physical i j
  · exact certificateDescendantBlock1_01_physical i j
  · exact certificateDescendantBlock1_02_physical i j
  · exact certificateDescendantBlock1_03_physical i j
  · exact certificateDescendantBlock1_04_physical i j
  · exact certificateDescendantBlock1_05_physical i j
  · exact certificateDescendantBlock1_06_physical i j
  · exact certificateDescendantBlock1_07_physical i j
  · exact certificateDescendantBlock1_08_physical i j
  · exact certificateDescendantBlock1_09_physical i j
  · exact certificateDescendantBlock1_10_physical i j
  · exact certificateDescendantBlock1_11_physical i j
  · exact certificateDescendantBlock1_12_physical i j
  · exact certificateDescendantBlock1_13_physical i j
  · exact certificateDescendantBlock1_14_physical i j
  · exact certificateDescendantBlock1_15_physical i j
  · exact certificateDescendantBlock1_16_physical i j
  · exact certificateDescendantBlock1_17_physical i j
  · exact certificateDescendantBlock1_18_physical i j
  · exact certificateDescendantBlock1_19_physical i j
  · exact certificateDescendantBlock1_20_physical i j
  · exact certificateDescendantBlock1_21_physical i j
  · exact certificateDescendantBlock1_22_physical i j
  · exact certificateDescendantBlock1_23_physical i j
  · exact certificateDescendantBlock1_24_physical i j
  · exact certificateDescendantBlock1_25_physical i j
  · exact certificateDescendantBlock1_26_physical i j
  · exact certificateDescendantBlock1_27_physical i j
  · exact certificateDescendantBlock1_28_physical i j
  · exact certificateDescendantBlock1_29_physical i j
  · exact certificateDescendantBlock1_30_physical i j
  · exact certificateDescendantBlock1_31_physical i j
  · exact certificateDescendantBlock1_32_physical i j
  · exact certificateDescendantBlock1_33_physical i j
  · exact certificateDescendantBlock1_34_physical i j
  · exact certificateDescendantBlock1_35_physical i j
  · exact certificateDescendantBlock1_36_physical i j

theorem certificateDescendantMatrices1_inverse (b : Fin 37) :
    (certificateDescendantMatrices1 b).map (Int.cast : ℤ → ℚ) *
      certificateDescendantInverse1 b = 1 := by
  fin_cases b
  · exact certificateRationalBlock_inverse certificateDescendantBlockA1_00
      certificateDescendantBlockW1_00 216 (by decide)
      certificateDescendantBlock1_00_inverse
  · exact certificateRationalBlock_inverse certificateDescendantBlockA1_01
      certificateDescendantBlockW1_01 216 (by decide)
      certificateDescendantBlock1_01_inverse
  · exact certificateRationalBlock_inverse certificateDescendantBlockA1_02
      certificateDescendantBlockW1_02 216 (by decide)
      certificateDescendantBlock1_02_inverse
  · exact certificateRationalBlock_inverse certificateDescendantBlockA1_03
      certificateDescendantBlockW1_03 36 (by decide)
      certificateDescendantBlock1_03_inverse
  · exact certificateRationalBlock_inverse certificateDescendantBlockA1_04
      certificateDescendantBlockW1_04 1728 (by decide)
      certificateDescendantBlock1_04_inverse
  · exact certificateRationalBlock_inverse certificateDescendantBlockA1_05
      certificateDescendantBlockW1_05 12096 (by decide)
      certificateDescendantBlock1_05_inverse
  · exact certificateRationalBlock_inverse certificateDescendantBlockA1_06
      certificateDescendantBlockW1_06 6048 (by decide)
      certificateDescendantBlock1_06_inverse
  · exact certificateRationalBlock_inverse certificateDescendantBlockA1_07
      certificateDescendantBlockW1_07 2016 (by decide)
      certificateDescendantBlock1_07_inverse
  · exact certificateRationalBlock_inverse certificateDescendantBlockA1_08
      certificateDescendantBlockW1_08 72 (by decide)
      certificateDescendantBlock1_08_inverse
  · exact certificateRationalBlock_inverse certificateDescendantBlockA1_09
      certificateDescendantBlockW1_09 8640 (by decide)
      certificateDescendantBlock1_09_inverse
  · exact certificateRationalBlock_inverse certificateDescendantBlockA1_10
      certificateDescendantBlockW1_10 36288 (by decide)
      certificateDescendantBlock1_10_inverse
  · exact certificateRationalBlock_inverse certificateDescendantBlockA1_11
      certificateDescendantBlockW1_11 90720 (by decide)
      certificateDescendantBlock1_11_inverse
  · exact certificateRationalBlock_inverse certificateDescendantBlockA1_12
      certificateDescendantBlockW1_12 90720 (by decide)
      certificateDescendantBlock1_12_inverse
  · exact certificateRationalBlock_inverse certificateDescendantBlockA1_13
      certificateDescendantBlockW1_13 3024 (by decide)
      certificateDescendantBlock1_13_inverse
  · exact certificateRationalBlock_inverse certificateDescendantBlockA1_14
      certificateDescendantBlockW1_14 72 (by decide)
      certificateDescendantBlock1_14_inverse
  · exact certificateRationalBlock_inverse certificateDescendantBlockA1_15
      certificateDescendantBlockW1_15 4320 (by decide)
      certificateDescendantBlock1_15_inverse
  · exact certificateRationalBlock_inverse certificateDescendantBlockA1_16
      certificateDescendantBlockW1_16 60480 (by decide)
      certificateDescendantBlock1_16_inverse
  · exact certificateRationalBlock_inverse certificateDescendantBlockA1_17
      certificateDescendantBlockW1_17 30240 (by decide)
      certificateDescendantBlock1_17_inverse
  · exact certificateRationalBlock_inverse certificateDescendantBlockA1_18
      certificateDescendantBlockW1_18 15120 (by decide)
      certificateDescendantBlock1_18_inverse
  · exact certificateRationalBlock_inverse certificateDescendantBlockA1_19
      certificateDescendantBlockW1_19 15120 (by decide)
      certificateDescendantBlock1_19_inverse
  · exact certificateRationalBlock_inverse certificateDescendantBlockA1_20
      certificateDescendantBlockW1_20 504 (by decide)
      certificateDescendantBlock1_20_inverse
  · exact certificateRationalBlock_inverse certificateDescendantBlockA1_21
      certificateDescendantBlockW1_21 6 (by decide)
      certificateDescendantBlock1_21_inverse
  · exact certificateRationalBlock_inverse certificateDescendantBlockA1_22
      certificateDescendantBlockW1_22 720 (by decide)
      certificateDescendantBlock1_22_inverse
  · exact certificateRationalBlock_inverse certificateDescendantBlockA1_23
      certificateDescendantBlockW1_23 3024 (by decide)
      certificateDescendantBlock1_23_inverse
  · exact certificateRationalBlock_inverse certificateDescendantBlockA1_24
      certificateDescendantBlockW1_24 15120 (by decide)
      certificateDescendantBlock1_24_inverse
  · exact certificateRationalBlock_inverse certificateDescendantBlockA1_25
      certificateDescendantBlockW1_25 7560 (by decide)
      certificateDescendantBlock1_25_inverse
  · exact certificateRationalBlock_inverse certificateDescendantBlockA1_26
      certificateDescendantBlockW1_26 504 (by decide)
      certificateDescendantBlock1_26_inverse
  · exact certificateRationalBlock_inverse certificateDescendantBlockA1_27
      certificateDescendantBlockW1_27 6 (by decide)
      certificateDescendantBlock1_27_inverse
  · exact certificateRationalBlock_inverse certificateDescendantBlockA1_28
      certificateDescendantBlockW1_28 72 (by decide)
      certificateDescendantBlock1_28_inverse
  · exact certificateRationalBlock_inverse certificateDescendantBlockA1_29
      certificateDescendantBlockW1_29 504 (by decide)
      certificateDescendantBlock1_29_inverse
  · exact certificateRationalBlock_inverse certificateDescendantBlockA1_30
      certificateDescendantBlockW1_30 504 (by decide)
      certificateDescendantBlock1_30_inverse
  · exact certificateRationalBlock_inverse certificateDescendantBlockA1_31
      certificateDescendantBlockW1_31 84 (by decide)
      certificateDescendantBlock1_31_inverse
  · exact certificateRationalBlock_inverse certificateDescendantBlockA1_32
      certificateDescendantBlockW1_32 3 (by decide)
      certificateDescendantBlock1_32_inverse
  · exact certificateRationalBlock_inverse certificateDescendantBlockA1_33
      certificateDescendantBlockW1_33 6 (by decide)
      certificateDescendantBlock1_33_inverse
  · exact certificateRationalBlock_inverse certificateDescendantBlockA1_34
      certificateDescendantBlockW1_34 6 (by decide)
      certificateDescendantBlock1_34_inverse
  · exact certificateRationalBlock_inverse certificateDescendantBlockA1_35
      certificateDescendantBlockW1_35 3 (by decide)
      certificateDescendantBlock1_35_inverse
  · exact certificateRationalBlock_inverse certificateDescendantBlockA1_36
      certificateDescendantBlockW1_36 1 (by decide)
      certificateDescendantBlock1_36_inverse

/-- The literal physical integer descendant columns span the entire rational local space. -/
theorem certificateDescendantPhysical1_surjective :
    Function.Surjective (certificateDescendantPhysical1.map (Int.cast : ℤ → ℚ)).mulVec := by
  apply certificatePhysicalBlocks_surjective certificateDescendantSizes1
    certificateDescendantRow1 certificateDescendantRow1_bijective.surjective
    (certificateDescendantPhysical1.map (Int.cast : ℤ → ℚ))
    (fun b => (certificateDescendantMatrices1 b).map (Int.cast : ℤ → ℚ))
    certificateDescendantInverse1
  · have h := congrArg (fun M => M.map (Int.cast : ℤ → ℚ)) certificateDescendantPhysical1_blocks
    rw [Matrix.blockDiagonal'_map certificateDescendantMatrices1
      (Int.cast : ℤ → ℚ) Int.cast_zero] at h
    simpa only [Matrix.submatrix_map] using h
  · exact certificateDescendantMatrices1_inverse

end ThreeCopyQutritWerner
