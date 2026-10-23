module

public import ThreeCopyQutritWerner.CertificateDescendantGramCheck1_00
public import ThreeCopyQutritWerner.CertificateDescendantGramCheck1_01
public import ThreeCopyQutritWerner.CertificateDescendantGramCheck1_02
public import ThreeCopyQutritWerner.CertificateDescendantGramCheck1_03
public import ThreeCopyQutritWerner.CertificateDescendantGramCheck1_04
public import ThreeCopyQutritWerner.CertificateDescendantGramCheck1_05
public import ThreeCopyQutritWerner.CertificateDescendantGramCheck1_06
public import ThreeCopyQutritWerner.CertificateDescendantGramCheck1_07
public import ThreeCopyQutritWerner.CertificateDescendantGramCheck1_08
public import ThreeCopyQutritWerner.CertificateDescendantGramCheck1_09
public import ThreeCopyQutritWerner.CertificateDescendantGramCheck1_10
public import ThreeCopyQutritWerner.CertificateDescendantGramCheck1_11
public import ThreeCopyQutritWerner.CertificateDescendantGramCheck1_12
public import ThreeCopyQutritWerner.CertificateDescendantGramCheck1_13
public import ThreeCopyQutritWerner.CertificateDescendantGramCheck1_14
public import ThreeCopyQutritWerner.CertificateDescendantGramCheck1_15
public import ThreeCopyQutritWerner.CertificateDescendantGramCheck1_16
public import ThreeCopyQutritWerner.CertificateDescendantGramCheck1_17
public import ThreeCopyQutritWerner.CertificateDescendantGramCheck1_18
public import ThreeCopyQutritWerner.CertificateDescendantGramCheck1_19
public import ThreeCopyQutritWerner.CertificateDescendantGramCheck1_20
public import ThreeCopyQutritWerner.CertificateDescendantGramCheck1_21
public import ThreeCopyQutritWerner.CertificateDescendantGramCheck1_22
public import ThreeCopyQutritWerner.CertificateDescendantGramCheck1_23
public import ThreeCopyQutritWerner.CertificateDescendantGramCheck1_24
public import ThreeCopyQutritWerner.CertificateDescendantGramCheck1_25
public import ThreeCopyQutritWerner.CertificateDescendantGramCheck1_26
public import ThreeCopyQutritWerner.CertificateDescendantGramCheck1_27
public import ThreeCopyQutritWerner.CertificateDescendantGramCheck1_28
public import ThreeCopyQutritWerner.CertificateDescendantGramCheck1_29
public import ThreeCopyQutritWerner.CertificateDescendantGramCheck1_30
public import ThreeCopyQutritWerner.CertificateDescendantGramCheck1_31
public import ThreeCopyQutritWerner.CertificateDescendantGramCheck1_32
public import ThreeCopyQutritWerner.CertificateDescendantGramCheck1_33
public import ThreeCopyQutritWerner.CertificateDescendantGramCheck1_34
public import ThreeCopyQutritWerner.CertificateDescendantGramCheck1_35
public import ThreeCopyQutritWerner.CertificateDescendantGramCheck1_36

@[expose] public section


/-! Exact physical Gram factorization in the original complete-frame basis. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

theorem certificateDescendantGram1_blocks (b : Fin 37) :
    (certificateDescendantMatrices1 b)ᵀ * certificateDescendantMatrices1 b =
      certificateDescendantGram1Metric.submatrix (fun j => certificateDescendantGram1Index ⟨b, j⟩) (fun j => certificateDescendantGram1Index ⟨b, j⟩) := by
  fin_cases b
  · exact certificateDescendantGramBlock1_00
  · exact certificateDescendantGramBlock1_01
  · exact certificateDescendantGramBlock1_02
  · exact certificateDescendantGramBlock1_03
  · exact certificateDescendantGramBlock1_04
  · exact certificateDescendantGramBlock1_05
  · exact certificateDescendantGramBlock1_06
  · exact certificateDescendantGramBlock1_07
  · exact certificateDescendantGramBlock1_08
  · exact certificateDescendantGramBlock1_09
  · exact certificateDescendantGramBlock1_10
  · exact certificateDescendantGramBlock1_11
  · exact certificateDescendantGramBlock1_12
  · exact certificateDescendantGramBlock1_13
  · exact certificateDescendantGramBlock1_14
  · exact certificateDescendantGramBlock1_15
  · exact certificateDescendantGramBlock1_16
  · exact certificateDescendantGramBlock1_17
  · exact certificateDescendantGramBlock1_18
  · exact certificateDescendantGramBlock1_19
  · exact certificateDescendantGramBlock1_20
  · exact certificateDescendantGramBlock1_21
  · exact certificateDescendantGramBlock1_22
  · exact certificateDescendantGramBlock1_23
  · exact certificateDescendantGramBlock1_24
  · exact certificateDescendantGramBlock1_25
  · exact certificateDescendantGramBlock1_26
  · exact certificateDescendantGramBlock1_27
  · exact certificateDescendantGramBlock1_28
  · exact certificateDescendantGramBlock1_29
  · exact certificateDescendantGramBlock1_30
  · exact certificateDescendantGramBlock1_31
  · exact certificateDescendantGramBlock1_32
  · exact certificateDescendantGramBlock1_33
  · exact certificateDescendantGramBlock1_34
  · exact certificateDescendantGramBlock1_35
  · exact certificateDescendantGramBlock1_36

theorem certificateDescendantGram1_weight_metric :
    Matrix.blockDiagonal' (fun b => (certificateDescendantMatrices1 b)ᵀ * certificateDescendantMatrices1 b) =
      certificateDescendantGram1Metric.submatrix certificateDescendantGram1Index certificateDescendantGram1Index := by
  ext ⟨b, i⟩ ⟨c, j⟩
  by_cases h : b = c
  · subst c
    rw [Matrix.blockDiagonal'_apply_eq]
    exact congrFun (congrFun (certificateDescendantGram1_blocks b) i) j
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ h]
    symm
    apply certificateRepeatedFrameMetric_zero
    apply certificateDescendantGram1K_off_weight
    rw [certificateDescendantGram1Weight_index, certificateDescendantGram1Weight_index]
    exact h

/-- The literal full physical descendant Gram, including every cross-type zero. -/
theorem certificateDescendantGram1_physical :
    certificateDescendantFrames1Matrixᵀ * certificateDescendantFrames1Matrix = certificateDescendantGram1Metric := by
  apply certificateGram_of_columns certificateDescendantFrames1Matrix certificateDescendantPhysical1
    certificateDescendantGram1Index certificateDescendantGram1Index_surjective
    (Matrix.ext certificateDescendantFrames1Matrix_bound)
  rw [certificateGram_of_weight_blocks certificateDescendantSizes1
    certificateDescendantRow1 certificateDescendantRow1_bijective _ _
    certificateDescendantPhysical1_blocks]
  exact certificateDescendantGram1_weight_metric

end ThreeCopyQutritWerner
