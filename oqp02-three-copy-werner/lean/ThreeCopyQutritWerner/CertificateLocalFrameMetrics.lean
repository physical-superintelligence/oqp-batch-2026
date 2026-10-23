module

public import ThreeCopyQutritWerner.CertificateFrameMetrics

@[expose] public section


/-!
Exact identity-row certificates for all 22 archive frames and positivity of
their original complex Gram metrics. Each identity is checked
with ordinary kernel `decide`, not trusted from the generator.
These local metrics are not the final endpoint Gram certificate.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

open scoped Matrix ComplexOrder

namespace ThreeCopyQutritWerner

def certificateLocalPivots0_0 : Fin 1 → (Fin 6 → Fin 3) :=
  ![![2, 2, 2, 2, 2, 0]]

theorem certificateLocalFrame0_0_pivots :
    certificateLocalFrame0_0.submatrix certificateLocalPivots0_0 id = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- Positivity of the original metric for sector 0, type 0. -/
theorem certificateLocalGram0_0_posDef :
    (certificateLocalGram0_0.map (Int.cast : ℤ → ℂ)).PosDef :=
  certificateLocalMetric_posDef_of_pivots certificateLocalFrame0_0
    certificateLocalGram0_0 certificateLocalPivots0_0
    certificateLocalGram0_0_correct certificateLocalFrame0_0_pivots

def certificateLocalPivots0_1 : Fin 4 → (Fin 6 → Fin 3) :=
  ![![2, 2, 1, 2, 2, 0],
    ![2, 2, 2, 1, 2, 0],
    ![2, 2, 2, 2, 1, 0],
    ![1, 2, 2, 2, 2, 0]]

theorem certificateLocalFrame0_1_pivots :
    certificateLocalFrame0_1.submatrix certificateLocalPivots0_1 id = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- Positivity of the original metric for sector 0, type 1. -/
theorem certificateLocalGram0_1_posDef :
    (certificateLocalGram0_1.map (Int.cast : ℤ → ℂ)).PosDef :=
  certificateLocalMetric_posDef_of_pivots certificateLocalFrame0_1
    certificateLocalGram0_1 certificateLocalPivots0_1
    certificateLocalGram0_1_correct certificateLocalFrame0_1_pivots

def certificateLocalPivots0_2 : Fin 5 → (Fin 6 → Fin 3) :=
  ![![2, 2, 0, 2, 2, 0],
    ![2, 2, 2, 0, 2, 0],
    ![2, 2, 2, 2, 0, 0],
    ![0, 2, 2, 2, 2, 0],
    ![2, 2, 2, 2, 2, 2]]

theorem certificateLocalFrame0_2_pivots :
    certificateLocalFrame0_2.submatrix certificateLocalPivots0_2 id = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- Positivity of the original metric for sector 0, type 2. -/
theorem certificateLocalGram0_2_posDef :
    (certificateLocalGram0_2.map (Int.cast : ℤ → ℂ)).PosDef :=
  certificateLocalMetric_posDef_of_pivots certificateLocalFrame0_2
    certificateLocalGram0_2 certificateLocalPivots0_2
    certificateLocalGram0_2_correct certificateLocalFrame0_2_pivots

def certificateLocalPivots0_3 : Fin 5 → (Fin 6 → Fin 3) :=
  ![![2, 2, 1, 2, 1, 0],
    ![1, 2, 1, 2, 2, 0],
    ![2, 2, 2, 1, 1, 0],
    ![1, 2, 2, 1, 2, 0],
    ![1, 2, 2, 2, 1, 0]]

theorem certificateLocalFrame0_3_pivots :
    certificateLocalFrame0_3.submatrix certificateLocalPivots0_3 id = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- Positivity of the original metric for sector 0, type 3. -/
theorem certificateLocalGram0_3_posDef :
    (certificateLocalGram0_3.map (Int.cast : ℤ → ℂ)).PosDef :=
  certificateLocalMetric_posDef_of_pivots certificateLocalFrame0_3
    certificateLocalGram0_3 certificateLocalPivots0_3
    certificateLocalGram0_3_correct certificateLocalFrame0_3_pivots

def certificateLocalPivots0_4 : Fin 15 → (Fin 6 → Fin 3) :=
  ![![2, 2, 1, 0, 2, 0],
    ![2, 2, 1, 2, 0, 0],
    ![0, 2, 1, 2, 2, 0],
    ![2, 2, 2, 1, 0, 0],
    ![0, 2, 2, 1, 2, 0],
    ![0, 2, 2, 2, 1, 0],
    ![2, 2, 1, 2, 1, 1],
    ![1, 2, 1, 2, 2, 1],
    ![2, 2, 2, 1, 1, 1],
    ![1, 2, 2, 1, 2, 1],
    ![1, 2, 2, 2, 1, 1],
    ![2, 2, 1, 2, 2, 2],
    ![2, 2, 2, 1, 2, 2],
    ![2, 2, 2, 2, 1, 2],
    ![1, 2, 2, 2, 2, 2]]

theorem certificateLocalFrame0_4_pivots :
    certificateLocalFrame0_4.submatrix certificateLocalPivots0_4 id = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- Positivity of the original metric for sector 0, type 4. -/
theorem certificateLocalGram0_4_posDef :
    (certificateLocalGram0_4.map (Int.cast : ℤ → ℂ)).PosDef :=
  certificateLocalMetric_posDef_of_pivots certificateLocalFrame0_4
    certificateLocalGram0_4 certificateLocalPivots0_4
    certificateLocalGram0_4_correct certificateLocalFrame0_4_pivots

def certificateLocalPivots0_5 : Fin 10 → (Fin 6 → Fin 3) :=
  ![![1, 2, 1, 0, 2, 0],
    ![1, 2, 1, 2, 0, 0],
    ![0, 1, 2, 1, 2, 0],
    ![1, 2, 2, 1, 0, 0],
    ![0, 1, 1, 2, 2, 0],
    ![1, 1, 2, 1, 2, 1],
    ![1, 2, 1, 2, 2, 2],
    ![1, 1, 1, 2, 2, 1],
    ![1, 2, 2, 1, 2, 2],
    ![1, 2, 2, 2, 1, 2]]

theorem certificateLocalFrame0_5_pivots :
    certificateLocalFrame0_5.submatrix certificateLocalPivots0_5 id = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- Positivity of the original metric for sector 0, type 5. -/
theorem certificateLocalGram0_5_posDef :
    (certificateLocalGram0_5.map (Int.cast : ℤ → ℂ)).PosDef :=
  certificateLocalMetric_posDef_of_pivots certificateLocalFrame0_5
    certificateLocalGram0_5 certificateLocalPivots0_5
    certificateLocalGram0_5_correct certificateLocalFrame0_5_pivots

def certificateLocalPivots0_6 : Fin 11 → (Fin 6 → Fin 3) :=
  ![![1, 2, 1, 0, 2, 1],
    ![1, 2, 1, 2, 0, 1],
    ![0, 2, 1, 2, 1, 1],
    ![1, 2, 2, 1, 0, 1],
    ![0, 2, 2, 1, 1, 1],
    ![2, 2, 1, 0, 2, 2],
    ![2, 2, 1, 2, 0, 2],
    ![0, 2, 1, 2, 2, 2],
    ![2, 2, 2, 1, 0, 2],
    ![0, 2, 2, 1, 2, 2],
    ![0, 2, 2, 2, 1, 2]]

theorem certificateLocalFrame0_6_pivots :
    certificateLocalFrame0_6.submatrix certificateLocalPivots0_6 id = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- Positivity of the original metric for sector 0, type 6. -/
theorem certificateLocalGram0_6_posDef :
    (certificateLocalGram0_6.map (Int.cast : ℤ → ℂ)).PosDef :=
  certificateLocalMetric_posDef_of_pivots certificateLocalFrame0_6
    certificateLocalGram0_6 certificateLocalPivots0_6
    certificateLocalGram0_6_correct certificateLocalFrame0_6_pivots

def certificateLocalPivots1_0 : Fin 1 → (Fin 6 → Fin 3) :=
  ![![0, 0, 0, 2, 2, 2]]

theorem certificateLocalFrame1_0_pivots :
    certificateLocalFrame1_0.submatrix certificateLocalPivots1_0 id = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- Positivity of the original metric for sector 1, type 0. -/
theorem certificateLocalGram1_0_posDef :
    (certificateLocalGram1_0.map (Int.cast : ℤ → ℂ)).PosDef :=
  certificateLocalMetric_posDef_of_pivots certificateLocalFrame1_0
    certificateLocalGram1_0 certificateLocalPivots1_0
    certificateLocalGram1_0_correct certificateLocalFrame1_0_pivots

def certificateLocalPivots1_1 : Fin 2 → (Fin 6 → Fin 3) :=
  ![![0, 0, 0, 2, 1, 2],
    ![0, 0, 0, 2, 2, 1]]

theorem certificateLocalFrame1_1_pivots :
    certificateLocalFrame1_1.submatrix certificateLocalPivots1_1 id = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- Positivity of the original metric for sector 1, type 1. -/
theorem certificateLocalGram1_1_posDef :
    (certificateLocalGram1_1.map (Int.cast : ℤ → ℂ)).PosDef :=
  certificateLocalMetric_posDef_of_pivots certificateLocalFrame1_1
    certificateLocalGram1_1 certificateLocalPivots1_1
    certificateLocalGram1_1_correct certificateLocalFrame1_1_pivots

def certificateLocalPivots1_2 : Fin 2 → (Fin 6 → Fin 3) :=
  ![![0, 1, 0, 2, 2, 2],
    ![1, 0, 0, 2, 2, 2]]

theorem certificateLocalFrame1_2_pivots :
    certificateLocalFrame1_2.submatrix certificateLocalPivots1_2 id = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- Positivity of the original metric for sector 1, type 2. -/
theorem certificateLocalGram1_2_posDef :
    (certificateLocalGram1_2.map (Int.cast : ℤ → ℂ)).PosDef :=
  certificateLocalMetric_posDef_of_pivots certificateLocalFrame1_2
    certificateLocalGram1_2 certificateLocalPivots1_2
    certificateLocalGram1_2_correct certificateLocalFrame1_2_pivots

def certificateLocalPivots1_3 : Fin 9 → (Fin 6 → Fin 3) :=
  ![![0, 0, 1, 2, 1, 2],
    ![0, 0, 1, 2, 2, 1],
    ![0, 0, 2, 2, 2, 2],
    ![0, 1, 0, 2, 1, 2],
    ![0, 1, 0, 2, 2, 1],
    ![0, 2, 0, 2, 2, 2],
    ![1, 0, 0, 2, 1, 2],
    ![1, 0, 0, 2, 2, 1],
    ![2, 0, 0, 2, 2, 2]]

theorem certificateLocalFrame1_3_pivots :
    certificateLocalFrame1_3.submatrix certificateLocalPivots1_3 id = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- Positivity of the original metric for sector 1, type 3. -/
theorem certificateLocalGram1_3_posDef :
    (certificateLocalGram1_3.map (Int.cast : ℤ → ℂ)).PosDef :=
  certificateLocalMetric_posDef_of_pivots certificateLocalFrame1_3
    certificateLocalGram1_3 certificateLocalPivots1_3
    certificateLocalGram1_3_correct certificateLocalFrame1_3_pivots

def certificateLocalPivots1_4 : Fin 7 → (Fin 6 → Fin 3) :=
  ![![0, 0, 0, 2, 1, 0],
    ![0, 0, 2, 2, 1, 2],
    ![0, 0, 2, 2, 2, 1],
    ![0, 2, 0, 2, 1, 2],
    ![0, 2, 0, 2, 2, 1],
    ![2, 0, 0, 2, 1, 2],
    ![2, 0, 0, 2, 2, 1]]

theorem certificateLocalFrame1_4_pivots :
    certificateLocalFrame1_4.submatrix certificateLocalPivots1_4 id = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- Positivity of the original metric for sector 1, type 4. -/
theorem certificateLocalGram1_4_posDef :
    (certificateLocalGram1_4.map (Int.cast : ℤ → ℂ)).PosDef :=
  certificateLocalMetric_posDef_of_pivots certificateLocalFrame1_4
    certificateLocalGram1_4 certificateLocalPivots1_4
    certificateLocalGram1_4_correct certificateLocalFrame1_4_pivots

def certificateLocalPivots1_5 : Fin 7 → (Fin 6 → Fin 3) :=
  ![![1, 0, 1, 2, 1, 2],
    ![1, 0, 1, 2, 2, 1],
    ![1, 0, 2, 2, 2, 2],
    ![1, 1, 0, 2, 1, 2],
    ![1, 1, 0, 2, 2, 1],
    ![1, 2, 0, 2, 2, 2],
    ![2, 1, 0, 2, 2, 2]]

theorem certificateLocalFrame1_5_pivots :
    certificateLocalFrame1_5.submatrix certificateLocalPivots1_5 id = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- Positivity of the original metric for sector 1, type 5. -/
theorem certificateLocalGram1_5_posDef :
    (certificateLocalGram1_5.map (Int.cast : ℤ → ℂ)).PosDef :=
  certificateLocalMetric_posDef_of_pivots certificateLocalFrame1_5
    certificateLocalGram1_5 certificateLocalPivots1_5
    certificateLocalGram1_5_correct certificateLocalFrame1_5_pivots

def certificateLocalPivots1_6 : Fin 17 → (Fin 6 → Fin 3) :=
  ![![0, 1, 0, 2, 1, 0],
    ![0, 1, 2, 2, 1, 2],
    ![0, 1, 2, 2, 2, 1],
    ![0, 2, 1, 2, 1, 2],
    ![0, 2, 1, 2, 2, 1],
    ![0, 2, 2, 2, 2, 2],
    ![1, 0, 0, 2, 1, 0],
    ![1, 0, 2, 2, 1, 2],
    ![1, 0, 2, 2, 2, 1],
    ![1, 2, 0, 2, 1, 2],
    ![1, 2, 0, 2, 2, 1],
    ![2, 0, 1, 2, 1, 2],
    ![2, 0, 1, 2, 2, 1],
    ![2, 0, 2, 2, 2, 2],
    ![2, 1, 0, 2, 1, 2],
    ![2, 1, 0, 2, 2, 1],
    ![2, 2, 0, 2, 2, 2]]

theorem certificateLocalFrame1_6_pivots :
    certificateLocalFrame1_6.submatrix certificateLocalPivots1_6 id = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- Positivity of the original metric for sector 1, type 6. -/
theorem certificateLocalGram1_6_posDef :
    (certificateLocalGram1_6.map (Int.cast : ℤ → ℂ)).PosDef :=
  certificateLocalMetric_posDef_of_pivots certificateLocalFrame1_6
    certificateLocalGram1_6 certificateLocalPivots1_6
    certificateLocalGram1_6_correct certificateLocalFrame1_6_pivots

def certificateLocalPivots1_7 : Fin 6 → (Fin 6 → Fin 3) :=
  ![![0, 1, 2, 0, 1, 2],
    ![0, 1, 0, 0, 1, 0],
    ![0, 1, 0, 0, 0, 1],
    ![0, 0, 1, 0, 1, 0],
    ![0, 0, 1, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0]]

theorem certificateLocalFrame1_7_pivots :
    certificateLocalFrame1_7.submatrix certificateLocalPivots1_7 id = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- Positivity of the original metric for sector 1, type 7. -/
theorem certificateLocalGram1_7_posDef :
    (certificateLocalGram1_7.map (Int.cast : ℤ → ℂ)).PosDef :=
  certificateLocalMetric_posDef_of_pivots certificateLocalFrame1_7
    certificateLocalGram1_7 certificateLocalPivots1_7
    certificateLocalGram1_7_correct certificateLocalFrame1_7_pivots

def certificateLocalPivots2_0 : Fin 1 → (Fin 6 → Fin 3) :=
  ![![0, 2, 2, 2, 2, 2]]

theorem certificateLocalFrame2_0_pivots :
    certificateLocalFrame2_0.submatrix certificateLocalPivots2_0 id = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- Positivity of the original metric for sector 2, type 0. -/
theorem certificateLocalGram2_0_posDef :
    (certificateLocalGram2_0.map (Int.cast : ℤ → ℂ)).PosDef :=
  certificateLocalMetric_posDef_of_pivots certificateLocalFrame2_0
    certificateLocalGram2_0 certificateLocalPivots2_0
    certificateLocalGram2_0_correct certificateLocalFrame2_0_pivots

def certificateLocalPivots2_1 : Fin 4 → (Fin 6 → Fin 3) :=
  ![![0, 2, 1, 2, 2, 2],
    ![0, 2, 2, 1, 2, 2],
    ![0, 2, 2, 2, 1, 2],
    ![0, 2, 2, 2, 2, 1]]

theorem certificateLocalFrame2_1_pivots :
    certificateLocalFrame2_1.submatrix certificateLocalPivots2_1 id = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- Positivity of the original metric for sector 2, type 1. -/
theorem certificateLocalGram2_1_posDef :
    (certificateLocalGram2_1.map (Int.cast : ℤ → ℂ)).PosDef :=
  certificateLocalMetric_posDef_of_pivots certificateLocalFrame2_1
    certificateLocalGram2_1 certificateLocalPivots2_1
    certificateLocalGram2_1_correct certificateLocalFrame2_1_pivots

def certificateLocalPivots2_2 : Fin 5 → (Fin 6 → Fin 3) :=
  ![![0, 2, 0, 2, 2, 2],
    ![0, 2, 2, 0, 2, 2],
    ![0, 2, 2, 2, 0, 2],
    ![0, 2, 2, 2, 2, 0],
    ![2, 2, 2, 2, 2, 2]]

theorem certificateLocalFrame2_2_pivots :
    certificateLocalFrame2_2.submatrix certificateLocalPivots2_2 id = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- Positivity of the original metric for sector 2, type 2. -/
theorem certificateLocalGram2_2_posDef :
    (certificateLocalGram2_2.map (Int.cast : ℤ → ℂ)).PosDef :=
  certificateLocalMetric_posDef_of_pivots certificateLocalFrame2_2
    certificateLocalGram2_2 certificateLocalPivots2_2
    certificateLocalGram2_2_correct certificateLocalFrame2_2_pivots

def certificateLocalPivots2_3 : Fin 5 → (Fin 6 → Fin 3) :=
  ![![0, 2, 1, 2, 1, 2],
    ![0, 2, 1, 2, 2, 1],
    ![0, 2, 2, 1, 1, 2],
    ![0, 2, 2, 1, 2, 1],
    ![0, 2, 2, 2, 1, 1]]

theorem certificateLocalFrame2_3_pivots :
    certificateLocalFrame2_3.submatrix certificateLocalPivots2_3 id = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- Positivity of the original metric for sector 2, type 3. -/
theorem certificateLocalGram2_3_posDef :
    (certificateLocalGram2_3.map (Int.cast : ℤ → ℂ)).PosDef :=
  certificateLocalMetric_posDef_of_pivots certificateLocalFrame2_3
    certificateLocalGram2_3 certificateLocalPivots2_3
    certificateLocalGram2_3_correct certificateLocalFrame2_3_pivots

def certificateLocalPivots2_4 : Fin 15 → (Fin 6 → Fin 3) :=
  ![![0, 2, 1, 0, 2, 2],
    ![0, 2, 1, 2, 0, 2],
    ![0, 2, 1, 2, 2, 0],
    ![0, 2, 2, 1, 0, 2],
    ![0, 2, 2, 1, 2, 0],
    ![0, 2, 2, 2, 1, 0],
    ![1, 2, 1, 2, 1, 2],
    ![1, 2, 1, 2, 2, 1],
    ![1, 2, 2, 1, 1, 2],
    ![1, 2, 2, 1, 2, 1],
    ![1, 2, 2, 2, 1, 1],
    ![2, 2, 1, 2, 2, 2],
    ![2, 2, 2, 1, 2, 2],
    ![2, 2, 2, 2, 1, 2],
    ![2, 2, 2, 2, 2, 1]]

theorem certificateLocalFrame2_4_pivots :
    certificateLocalFrame2_4.submatrix certificateLocalPivots2_4 id = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- Positivity of the original metric for sector 2, type 4. -/
theorem certificateLocalGram2_4_posDef :
    (certificateLocalGram2_4.map (Int.cast : ℤ → ℂ)).PosDef :=
  certificateLocalMetric_posDef_of_pivots certificateLocalFrame2_4
    certificateLocalGram2_4 certificateLocalPivots2_4
    certificateLocalGram2_4_correct certificateLocalFrame2_4_pivots

def certificateLocalPivots2_5 : Fin 10 → (Fin 6 → Fin 3) :=
  ![![0, 1, 2, 0, 1, 2],
    ![0, 1, 2, 1, 0, 2],
    ![0, 1, 2, 1, 2, 0],
    ![0, 1, 1, 2, 0, 2],
    ![0, 1, 1, 2, 2, 0],
    ![1, 1, 2, 1, 2, 1],
    ![1, 1, 2, 1, 1, 2],
    ![1, 1, 1, 2, 2, 1],
    ![1, 1, 1, 2, 1, 2],
    ![1, 1, 1, 1, 2, 2]]

theorem certificateLocalFrame2_5_pivots :
    certificateLocalFrame2_5.submatrix certificateLocalPivots2_5 id = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- Positivity of the original metric for sector 2, type 5. -/
theorem certificateLocalGram2_5_posDef :
    (certificateLocalGram2_5.map (Int.cast : ℤ → ℂ)).PosDef :=
  certificateLocalMetric_posDef_of_pivots certificateLocalFrame2_5
    certificateLocalGram2_5 certificateLocalPivots2_5
    certificateLocalGram2_5_correct certificateLocalFrame2_5_pivots

def certificateLocalPivots2_6 : Fin 11 → (Fin 6 → Fin 3) :=
  ![![1, 2, 1, 0, 2, 1],
    ![1, 2, 1, 2, 0, 1],
    ![1, 2, 1, 2, 1, 0],
    ![1, 2, 2, 1, 0, 1],
    ![1, 2, 2, 1, 1, 0],
    ![2, 2, 1, 0, 2, 2],
    ![2, 2, 1, 2, 0, 2],
    ![2, 2, 1, 2, 2, 0],
    ![2, 2, 2, 1, 0, 2],
    ![2, 2, 2, 1, 2, 0],
    ![2, 2, 2, 2, 1, 0]]

theorem certificateLocalFrame2_6_pivots :
    certificateLocalFrame2_6.submatrix certificateLocalPivots2_6 id = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- Positivity of the original metric for sector 2, type 6. -/
theorem certificateLocalGram2_6_posDef :
    (certificateLocalGram2_6.map (Int.cast : ℤ → ℂ)).PosDef :=
  certificateLocalMetric_posDef_of_pivots certificateLocalFrame2_6
    certificateLocalGram2_6 certificateLocalPivots2_6
    certificateLocalGram2_6_correct certificateLocalFrame2_6_pivots

end ThreeCopyQutritWerner
