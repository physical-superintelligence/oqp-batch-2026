module

public import ThreeCopyQutritWerner.CertificateDescendantBlockChecks

@[expose] public section


/-!
Exact sector-2 physical completeness from 33 finite integer inverse checks.
The columns here are the literal sparse descendant candidates; their separate
lowering-program theorem binds them to the original archive highest frames.
-/

noncomputable section

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

abbrev CertificateDescendantIndex2 := Σ b : Fin 33, Fin (certificateDescendantSizes2 b)

def certificateDescendantRow2 (r : CertificateDescendantIndex2) : CertificateLocalWord :=
  certificateDescendantBlockRows2 r.1 r.2

def certificateDescendantPhysical2 : Matrix CertificateLocalWord CertificateDescendantIndex2 ℤ :=
  fun w c => certificateSparseVector
    (certificateDescendantColumns2 (certificateDescendantBlockColumns2 c.1 c.2)) w

def certificateDescendantMatrices2 : ∀ b : Fin 33,
    Matrix (Fin (certificateDescendantSizes2 b)) (Fin (certificateDescendantSizes2 b)) ℤ := by
  exact
    Fin.cases (certificateDescendantBlockA2_00) <|
    Fin.cases (certificateDescendantBlockA2_01) <|
    Fin.cases (certificateDescendantBlockA2_02) <|
    Fin.cases (certificateDescendantBlockA2_03) <|
    Fin.cases (certificateDescendantBlockA2_04) <|
    Fin.cases (certificateDescendantBlockA2_05) <|
    Fin.cases (certificateDescendantBlockA2_06) <|
    Fin.cases (certificateDescendantBlockA2_07) <|
    Fin.cases (certificateDescendantBlockA2_08) <|
    Fin.cases (certificateDescendantBlockA2_09) <|
    Fin.cases (certificateDescendantBlockA2_10) <|
    Fin.cases (certificateDescendantBlockA2_11) <|
    Fin.cases (certificateDescendantBlockA2_12) <|
    Fin.cases (certificateDescendantBlockA2_13) <|
    Fin.cases (certificateDescendantBlockA2_14) <|
    Fin.cases (certificateDescendantBlockA2_15) <|
    Fin.cases (certificateDescendantBlockA2_16) <|
    Fin.cases (certificateDescendantBlockA2_17) <|
    Fin.cases (certificateDescendantBlockA2_18) <|
    Fin.cases (certificateDescendantBlockA2_19) <|
    Fin.cases (certificateDescendantBlockA2_20) <|
    Fin.cases (certificateDescendantBlockA2_21) <|
    Fin.cases (certificateDescendantBlockA2_22) <|
    Fin.cases (certificateDescendantBlockA2_23) <|
    Fin.cases (certificateDescendantBlockA2_24) <|
    Fin.cases (certificateDescendantBlockA2_25) <|
    Fin.cases (certificateDescendantBlockA2_26) <|
    Fin.cases (certificateDescendantBlockA2_27) <|
    Fin.cases (certificateDescendantBlockA2_28) <|
    Fin.cases (certificateDescendantBlockA2_29) <|
    Fin.cases (certificateDescendantBlockA2_30) <|
    Fin.cases (certificateDescendantBlockA2_31) <|
    Fin.cases (certificateDescendantBlockA2_32) <|
    Fin.rec0

def certificateDescendantInverse2 : ∀ b : Fin 33,
    Matrix (Fin (certificateDescendantSizes2 b)) (Fin (certificateDescendantSizes2 b)) ℚ := by
  exact
    Fin.cases ((120 : ℚ)⁻¹ • (certificateDescendantBlockW2_00.map (Int.cast : ℤ → ℚ))) <|
    Fin.cases ((120 : ℚ)⁻¹ • (certificateDescendantBlockW2_01.map (Int.cast : ℤ → ℚ))) <|
    Fin.cases ((240 : ℚ)⁻¹ • (certificateDescendantBlockW2_02.map (Int.cast : ℤ → ℚ))) <|
    Fin.cases ((1680 : ℚ)⁻¹ • (certificateDescendantBlockW2_03.map (Int.cast : ℤ → ℚ))) <|
    Fin.cases ((120 : ℚ)⁻¹ • (certificateDescendantBlockW2_04.map (Int.cast : ℤ → ℚ))) <|
    Fin.cases ((1080 : ℚ)⁻¹ • (certificateDescendantBlockW2_05.map (Int.cast : ℤ → ℚ))) <|
    Fin.cases ((15120 : ℚ)⁻¹ • (certificateDescendantBlockW2_06.map (Int.cast : ℤ → ℚ))) <|
    Fin.cases ((15120 : ℚ)⁻¹ • (certificateDescendantBlockW2_07.map (Int.cast : ℤ → ℚ))) <|
    Fin.cases ((180 : ℚ)⁻¹ • (certificateDescendantBlockW2_08.map (Int.cast : ℤ → ℚ))) <|
    Fin.cases ((4320 : ℚ)⁻¹ • (certificateDescendantBlockW2_09.map (Int.cast : ℤ → ℚ))) <|
    Fin.cases ((15120 : ℚ)⁻¹ • (certificateDescendantBlockW2_10.map (Int.cast : ℤ → ℚ))) <|
    Fin.cases ((15120 : ℚ)⁻¹ • (certificateDescendantBlockW2_11.map (Int.cast : ℤ → ℚ))) <|
    Fin.cases ((2520 : ℚ)⁻¹ • (certificateDescendantBlockW2_12.map (Int.cast : ℤ → ℚ))) <|
    Fin.cases ((180 : ℚ)⁻¹ • (certificateDescendantBlockW2_13.map (Int.cast : ℤ → ℚ))) <|
    Fin.cases ((1200 : ℚ)⁻¹ • (certificateDescendantBlockW2_14.map (Int.cast : ℤ → ℚ))) <|
    Fin.cases ((15120 : ℚ)⁻¹ • (certificateDescendantBlockW2_15.map (Int.cast : ℤ → ℚ))) <|
    Fin.cases ((5040 : ℚ)⁻¹ • (certificateDescendantBlockW2_16.map (Int.cast : ℤ → ℚ))) <|
    Fin.cases ((2520 : ℚ)⁻¹ • (certificateDescendantBlockW2_17.map (Int.cast : ℤ → ℚ))) <|
    Fin.cases ((2520 : ℚ)⁻¹ • (certificateDescendantBlockW2_18.map (Int.cast : ℤ → ℚ))) <|
    Fin.cases ((10 : ℚ)⁻¹ • (certificateDescendantBlockW2_19.map (Int.cast : ℤ → ℚ))) <|
    Fin.cases ((720 : ℚ)⁻¹ • (certificateDescendantBlockW2_20.map (Int.cast : ℤ → ℚ))) <|
    Fin.cases ((1680 : ℚ)⁻¹ • (certificateDescendantBlockW2_21.map (Int.cast : ℤ → ℚ))) <|
    Fin.cases ((5040 : ℚ)⁻¹ • (certificateDescendantBlockW2_22.map (Int.cast : ℤ → ℚ))) <|
    Fin.cases ((2520 : ℚ)⁻¹ • (certificateDescendantBlockW2_23.map (Int.cast : ℤ → ℚ))) <|
    Fin.cases ((2520 : ℚ)⁻¹ • (certificateDescendantBlockW2_24.map (Int.cast : ℤ → ℚ))) <|
    Fin.cases ((70 : ℚ)⁻¹ • (certificateDescendantBlockW2_25.map (Int.cast : ℤ → ℚ))) <|
    Fin.cases ((1 : ℚ)⁻¹ • (certificateDescendantBlockW2_26.map (Int.cast : ℤ → ℚ))) <|
    Fin.cases ((120 : ℚ)⁻¹ • (certificateDescendantBlockW2_27.map (Int.cast : ℤ → ℚ))) <|
    Fin.cases ((120 : ℚ)⁻¹ • (certificateDescendantBlockW2_28.map (Int.cast : ℤ → ℚ))) <|
    Fin.cases ((60 : ℚ)⁻¹ • (certificateDescendantBlockW2_29.map (Int.cast : ℤ → ℚ))) <|
    Fin.cases ((60 : ℚ)⁻¹ • (certificateDescendantBlockW2_30.map (Int.cast : ℤ → ℚ))) <|
    Fin.cases ((5 : ℚ)⁻¹ • (certificateDescendantBlockW2_31.map (Int.cast : ℤ → ℚ))) <|
    Fin.cases ((1 : ℚ)⁻¹ • (certificateDescendantBlockW2_32.map (Int.cast : ℤ → ℚ))) <|
    Fin.rec0

theorem certificateDescendantWeights2_injective :
    Function.Injective certificateDescendantWeights2 := by decide

theorem certificateDescendantBlockRows2_injective (b : Fin 33) :
    Function.Injective (certificateDescendantBlockRows2 b) := by
  fin_cases b
  · exact certificateDescendantBlock2_00_rows_injective
  · exact certificateDescendantBlock2_01_rows_injective
  · exact certificateDescendantBlock2_02_rows_injective
  · exact certificateDescendantBlock2_03_rows_injective
  · exact certificateDescendantBlock2_04_rows_injective
  · exact certificateDescendantBlock2_05_rows_injective
  · exact certificateDescendantBlock2_06_rows_injective
  · exact certificateDescendantBlock2_07_rows_injective
  · exact certificateDescendantBlock2_08_rows_injective
  · exact certificateDescendantBlock2_09_rows_injective
  · exact certificateDescendantBlock2_10_rows_injective
  · exact certificateDescendantBlock2_11_rows_injective
  · exact certificateDescendantBlock2_12_rows_injective
  · exact certificateDescendantBlock2_13_rows_injective
  · exact certificateDescendantBlock2_14_rows_injective
  · exact certificateDescendantBlock2_15_rows_injective
  · exact certificateDescendantBlock2_16_rows_injective
  · exact certificateDescendantBlock2_17_rows_injective
  · exact certificateDescendantBlock2_18_rows_injective
  · exact certificateDescendantBlock2_19_rows_injective
  · exact certificateDescendantBlock2_20_rows_injective
  · exact certificateDescendantBlock2_21_rows_injective
  · exact certificateDescendantBlock2_22_rows_injective
  · exact certificateDescendantBlock2_23_rows_injective
  · exact certificateDescendantBlock2_24_rows_injective
  · exact certificateDescendantBlock2_25_rows_injective
  · exact certificateDescendantBlock2_26_rows_injective
  · exact certificateDescendantBlock2_27_rows_injective
  · exact certificateDescendantBlock2_28_rows_injective
  · exact certificateDescendantBlock2_29_rows_injective
  · exact certificateDescendantBlock2_30_rows_injective
  · exact certificateDescendantBlock2_31_rows_injective
  · exact certificateDescendantBlock2_32_rows_injective

theorem certificateDescendantBlockRows2_weight (b : Fin 33)
    (i : Fin (certificateDescendantSizes2 b)) :
    (fun r => certificateLocalWeight {0} (certificateDescendantBlockRows2 b i) r) =
      certificateDescendantWeights2 b := by
  fin_cases b
  · exact certificateDescendantBlock2_00_row_weight i
  · exact certificateDescendantBlock2_01_row_weight i
  · exact certificateDescendantBlock2_02_row_weight i
  · exact certificateDescendantBlock2_03_row_weight i
  · exact certificateDescendantBlock2_04_row_weight i
  · exact certificateDescendantBlock2_05_row_weight i
  · exact certificateDescendantBlock2_06_row_weight i
  · exact certificateDescendantBlock2_07_row_weight i
  · exact certificateDescendantBlock2_08_row_weight i
  · exact certificateDescendantBlock2_09_row_weight i
  · exact certificateDescendantBlock2_10_row_weight i
  · exact certificateDescendantBlock2_11_row_weight i
  · exact certificateDescendantBlock2_12_row_weight i
  · exact certificateDescendantBlock2_13_row_weight i
  · exact certificateDescendantBlock2_14_row_weight i
  · exact certificateDescendantBlock2_15_row_weight i
  · exact certificateDescendantBlock2_16_row_weight i
  · exact certificateDescendantBlock2_17_row_weight i
  · exact certificateDescendantBlock2_18_row_weight i
  · exact certificateDescendantBlock2_19_row_weight i
  · exact certificateDescendantBlock2_20_row_weight i
  · exact certificateDescendantBlock2_21_row_weight i
  · exact certificateDescendantBlock2_22_row_weight i
  · exact certificateDescendantBlock2_23_row_weight i
  · exact certificateDescendantBlock2_24_row_weight i
  · exact certificateDescendantBlock2_25_row_weight i
  · exact certificateDescendantBlock2_26_row_weight i
  · exact certificateDescendantBlock2_27_row_weight i
  · exact certificateDescendantBlock2_28_row_weight i
  · exact certificateDescendantBlock2_29_row_weight i
  · exact certificateDescendantBlock2_30_row_weight i
  · exact certificateDescendantBlock2_31_row_weight i
  · exact certificateDescendantBlock2_32_row_weight i

theorem certificateDescendantBlockColumns2_weight (b : Fin 33)
    (j : Fin (certificateDescendantSizes2 b)) :
    List.Forall (fun a => (fun r => certificateLocalWeight {0} a.1 r) =
      certificateDescendantWeights2 b)
      (certificateDescendantColumns2 (certificateDescendantBlockColumns2 b j)) := by
  fin_cases b
  · exact certificateDescendantBlock2_00_column_weight j
  · exact certificateDescendantBlock2_01_column_weight j
  · exact certificateDescendantBlock2_02_column_weight j
  · exact certificateDescendantBlock2_03_column_weight j
  · exact certificateDescendantBlock2_04_column_weight j
  · exact certificateDescendantBlock2_05_column_weight j
  · exact certificateDescendantBlock2_06_column_weight j
  · exact certificateDescendantBlock2_07_column_weight j
  · exact certificateDescendantBlock2_08_column_weight j
  · exact certificateDescendantBlock2_09_column_weight j
  · exact certificateDescendantBlock2_10_column_weight j
  · exact certificateDescendantBlock2_11_column_weight j
  · exact certificateDescendantBlock2_12_column_weight j
  · exact certificateDescendantBlock2_13_column_weight j
  · exact certificateDescendantBlock2_14_column_weight j
  · exact certificateDescendantBlock2_15_column_weight j
  · exact certificateDescendantBlock2_16_column_weight j
  · exact certificateDescendantBlock2_17_column_weight j
  · exact certificateDescendantBlock2_18_column_weight j
  · exact certificateDescendantBlock2_19_column_weight j
  · exact certificateDescendantBlock2_20_column_weight j
  · exact certificateDescendantBlock2_21_column_weight j
  · exact certificateDescendantBlock2_22_column_weight j
  · exact certificateDescendantBlock2_23_column_weight j
  · exact certificateDescendantBlock2_24_column_weight j
  · exact certificateDescendantBlock2_25_column_weight j
  · exact certificateDescendantBlock2_26_column_weight j
  · exact certificateDescendantBlock2_27_column_weight j
  · exact certificateDescendantBlock2_28_column_weight j
  · exact certificateDescendantBlock2_29_column_weight j
  · exact certificateDescendantBlock2_30_column_weight j
  · exact certificateDescendantBlock2_31_column_weight j
  · exact certificateDescendantBlock2_32_column_weight j

/-- All 729 physical words occur exactly once in the literal weight rows. -/
theorem certificateDescendantRow2_bijective : Function.Bijective certificateDescendantRow2 := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · exact certificateWeightRows_injective certificateDescendantSizes2
      certificateDescendantBlockRows2 (fun w => fun r => certificateLocalWeight {0} w r)
      certificateDescendantWeights2 certificateDescendantWeights2_injective
      certificateDescendantBlockRows2_injective certificateDescendantBlockRows2_weight
  · norm_num [CertificateDescendantIndex2, CertificateLocalWord, Fintype.card_sigma,
      Fintype.card_fun, certificateDescendantSizes2, Fin.sum_univ_succ]

theorem certificateDescendantPhysical2_blocks :
    certificateDescendantPhysical2.submatrix certificateDescendantRow2 id =
      Matrix.blockDiagonal' certificateDescendantMatrices2 := by
  apply certificateSparseWeightBlocks_diagonal certificateDescendantSizes2
    certificateDescendantBlockRows2
    (fun b j => certificateDescendantColumns2 (certificateDescendantBlockColumns2 b j))
    (fun w => fun r => certificateLocalWeight {0} w r) certificateDescendantWeights2
    certificateDescendantWeights2_injective certificateDescendantMatrices2
    certificateDescendantBlockRows2_weight certificateDescendantBlockColumns2_weight
  intro b i j
  fin_cases b
  · exact certificateDescendantBlock2_00_physical i j
  · exact certificateDescendantBlock2_01_physical i j
  · exact certificateDescendantBlock2_02_physical i j
  · exact certificateDescendantBlock2_03_physical i j
  · exact certificateDescendantBlock2_04_physical i j
  · exact certificateDescendantBlock2_05_physical i j
  · exact certificateDescendantBlock2_06_physical i j
  · exact certificateDescendantBlock2_07_physical i j
  · exact certificateDescendantBlock2_08_physical i j
  · exact certificateDescendantBlock2_09_physical i j
  · exact certificateDescendantBlock2_10_physical i j
  · exact certificateDescendantBlock2_11_physical i j
  · exact certificateDescendantBlock2_12_physical i j
  · exact certificateDescendantBlock2_13_physical i j
  · exact certificateDescendantBlock2_14_physical i j
  · exact certificateDescendantBlock2_15_physical i j
  · exact certificateDescendantBlock2_16_physical i j
  · exact certificateDescendantBlock2_17_physical i j
  · exact certificateDescendantBlock2_18_physical i j
  · exact certificateDescendantBlock2_19_physical i j
  · exact certificateDescendantBlock2_20_physical i j
  · exact certificateDescendantBlock2_21_physical i j
  · exact certificateDescendantBlock2_22_physical i j
  · exact certificateDescendantBlock2_23_physical i j
  · exact certificateDescendantBlock2_24_physical i j
  · exact certificateDescendantBlock2_25_physical i j
  · exact certificateDescendantBlock2_26_physical i j
  · exact certificateDescendantBlock2_27_physical i j
  · exact certificateDescendantBlock2_28_physical i j
  · exact certificateDescendantBlock2_29_physical i j
  · exact certificateDescendantBlock2_30_physical i j
  · exact certificateDescendantBlock2_31_physical i j
  · exact certificateDescendantBlock2_32_physical i j

theorem certificateDescendantMatrices2_inverse (b : Fin 33) :
    (certificateDescendantMatrices2 b).map (Int.cast : ℤ → ℚ) *
      certificateDescendantInverse2 b = 1 := by
  fin_cases b
  · exact certificateRationalBlock_inverse certificateDescendantBlockA2_00
      certificateDescendantBlockW2_00 120 (by decide)
      certificateDescendantBlock2_00_inverse
  · exact certificateRationalBlock_inverse certificateDescendantBlockA2_01
      certificateDescendantBlockW2_01 120 (by decide)
      certificateDescendantBlock2_01_inverse
  · exact certificateRationalBlock_inverse certificateDescendantBlockA2_02
      certificateDescendantBlockW2_02 240 (by decide)
      certificateDescendantBlock2_02_inverse
  · exact certificateRationalBlock_inverse certificateDescendantBlockA2_03
      certificateDescendantBlockW2_03 1680 (by decide)
      certificateDescendantBlock2_03_inverse
  · exact certificateRationalBlock_inverse certificateDescendantBlockA2_04
      certificateDescendantBlockW2_04 120 (by decide)
      certificateDescendantBlock2_04_inverse
  · exact certificateRationalBlock_inverse certificateDescendantBlockA2_05
      certificateDescendantBlockW2_05 1080 (by decide)
      certificateDescendantBlock2_05_inverse
  · exact certificateRationalBlock_inverse certificateDescendantBlockA2_06
      certificateDescendantBlockW2_06 15120 (by decide)
      certificateDescendantBlock2_06_inverse
  · exact certificateRationalBlock_inverse certificateDescendantBlockA2_07
      certificateDescendantBlockW2_07 15120 (by decide)
      certificateDescendantBlock2_07_inverse
  · exact certificateRationalBlock_inverse certificateDescendantBlockA2_08
      certificateDescendantBlockW2_08 180 (by decide)
      certificateDescendantBlock2_08_inverse
  · exact certificateRationalBlock_inverse certificateDescendantBlockA2_09
      certificateDescendantBlockW2_09 4320 (by decide)
      certificateDescendantBlock2_09_inverse
  · exact certificateRationalBlock_inverse certificateDescendantBlockA2_10
      certificateDescendantBlockW2_10 15120 (by decide)
      certificateDescendantBlock2_10_inverse
  · exact certificateRationalBlock_inverse certificateDescendantBlockA2_11
      certificateDescendantBlockW2_11 15120 (by decide)
      certificateDescendantBlock2_11_inverse
  · exact certificateRationalBlock_inverse certificateDescendantBlockA2_12
      certificateDescendantBlockW2_12 2520 (by decide)
      certificateDescendantBlock2_12_inverse
  · exact certificateRationalBlock_inverse certificateDescendantBlockA2_13
      certificateDescendantBlockW2_13 180 (by decide)
      certificateDescendantBlock2_13_inverse
  · exact certificateRationalBlock_inverse certificateDescendantBlockA2_14
      certificateDescendantBlockW2_14 1200 (by decide)
      certificateDescendantBlock2_14_inverse
  · exact certificateRationalBlock_inverse certificateDescendantBlockA2_15
      certificateDescendantBlockW2_15 15120 (by decide)
      certificateDescendantBlock2_15_inverse
  · exact certificateRationalBlock_inverse certificateDescendantBlockA2_16
      certificateDescendantBlockW2_16 5040 (by decide)
      certificateDescendantBlock2_16_inverse
  · exact certificateRationalBlock_inverse certificateDescendantBlockA2_17
      certificateDescendantBlockW2_17 2520 (by decide)
      certificateDescendantBlock2_17_inverse
  · exact certificateRationalBlock_inverse certificateDescendantBlockA2_18
      certificateDescendantBlockW2_18 2520 (by decide)
      certificateDescendantBlock2_18_inverse
  · exact certificateRationalBlock_inverse certificateDescendantBlockA2_19
      certificateDescendantBlockW2_19 10 (by decide)
      certificateDescendantBlock2_19_inverse
  · exact certificateRationalBlock_inverse certificateDescendantBlockA2_20
      certificateDescendantBlockW2_20 720 (by decide)
      certificateDescendantBlock2_20_inverse
  · exact certificateRationalBlock_inverse certificateDescendantBlockA2_21
      certificateDescendantBlockW2_21 1680 (by decide)
      certificateDescendantBlock2_21_inverse
  · exact certificateRationalBlock_inverse certificateDescendantBlockA2_22
      certificateDescendantBlockW2_22 5040 (by decide)
      certificateDescendantBlock2_22_inverse
  · exact certificateRationalBlock_inverse certificateDescendantBlockA2_23
      certificateDescendantBlockW2_23 2520 (by decide)
      certificateDescendantBlock2_23_inverse
  · exact certificateRationalBlock_inverse certificateDescendantBlockA2_24
      certificateDescendantBlockW2_24 2520 (by decide)
      certificateDescendantBlock2_24_inverse
  · exact certificateRationalBlock_inverse certificateDescendantBlockA2_25
      certificateDescendantBlockW2_25 70 (by decide)
      certificateDescendantBlock2_25_inverse
  · exact certificateRationalBlock_inverse certificateDescendantBlockA2_26
      certificateDescendantBlockW2_26 1 (by decide)
      certificateDescendantBlock2_26_inverse
  · exact certificateRationalBlock_inverse certificateDescendantBlockA2_27
      certificateDescendantBlockW2_27 120 (by decide)
      certificateDescendantBlock2_27_inverse
  · exact certificateRationalBlock_inverse certificateDescendantBlockA2_28
      certificateDescendantBlockW2_28 120 (by decide)
      certificateDescendantBlock2_28_inverse
  · exact certificateRationalBlock_inverse certificateDescendantBlockA2_29
      certificateDescendantBlockW2_29 60 (by decide)
      certificateDescendantBlock2_29_inverse
  · exact certificateRationalBlock_inverse certificateDescendantBlockA2_30
      certificateDescendantBlockW2_30 60 (by decide)
      certificateDescendantBlock2_30_inverse
  · exact certificateRationalBlock_inverse certificateDescendantBlockA2_31
      certificateDescendantBlockW2_31 5 (by decide)
      certificateDescendantBlock2_31_inverse
  · exact certificateRationalBlock_inverse certificateDescendantBlockA2_32
      certificateDescendantBlockW2_32 1 (by decide)
      certificateDescendantBlock2_32_inverse

/-- The literal physical integer descendant columns span the entire rational local space. -/
theorem certificateDescendantPhysical2_surjective :
    Function.Surjective (certificateDescendantPhysical2.map (Int.cast : ℤ → ℚ)).mulVec := by
  apply certificatePhysicalBlocks_surjective certificateDescendantSizes2
    certificateDescendantRow2 certificateDescendantRow2_bijective.surjective
    (certificateDescendantPhysical2.map (Int.cast : ℤ → ℚ))
    (fun b => (certificateDescendantMatrices2 b).map (Int.cast : ℤ → ℚ))
    certificateDescendantInverse2
  · have h := congrArg (fun M => M.map (Int.cast : ℤ → ℚ)) certificateDescendantPhysical2_blocks
    rw [Matrix.blockDiagonal'_map certificateDescendantMatrices2
      (Int.cast : ℤ → ℚ) Int.cast_zero] at h
    simpa only [Matrix.submatrix_map] using h
  · exact certificateDescendantMatrices2_inverse

end ThreeCopyQutritWerner
