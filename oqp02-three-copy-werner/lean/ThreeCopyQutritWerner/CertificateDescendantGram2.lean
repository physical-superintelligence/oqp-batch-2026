module

public import ThreeCopyQutritWerner.CertificateDescendantGramCheck2_00
public import ThreeCopyQutritWerner.CertificateDescendantGramCheck2_01
public import ThreeCopyQutritWerner.CertificateDescendantGramCheck2_02
public import ThreeCopyQutritWerner.CertificateDescendantGramCheck2_03
public import ThreeCopyQutritWerner.CertificateDescendantGramCheck2_04
public import ThreeCopyQutritWerner.CertificateDescendantGramCheck2_05
public import ThreeCopyQutritWerner.CertificateDescendantGramCheck2_06
public import ThreeCopyQutritWerner.CertificateDescendantGramCheck2_07
public import ThreeCopyQutritWerner.CertificateDescendantGramCheck2_08
public import ThreeCopyQutritWerner.CertificateDescendantGramCheck2_09
public import ThreeCopyQutritWerner.CertificateDescendantGramCheck2_10
public import ThreeCopyQutritWerner.CertificateDescendantGramCheck2_11
public import ThreeCopyQutritWerner.CertificateDescendantGramCheck2_12
public import ThreeCopyQutritWerner.CertificateDescendantGramCheck2_13
public import ThreeCopyQutritWerner.CertificateDescendantGramCheck2_14
public import ThreeCopyQutritWerner.CertificateDescendantGramCheck2_15
public import ThreeCopyQutritWerner.CertificateDescendantGramCheck2_16
public import ThreeCopyQutritWerner.CertificateDescendantGramCheck2_17
public import ThreeCopyQutritWerner.CertificateDescendantGramCheck2_18
public import ThreeCopyQutritWerner.CertificateDescendantGramCheck2_19
public import ThreeCopyQutritWerner.CertificateDescendantGramCheck2_20
public import ThreeCopyQutritWerner.CertificateDescendantGramCheck2_21
public import ThreeCopyQutritWerner.CertificateDescendantGramCheck2_22
public import ThreeCopyQutritWerner.CertificateDescendantGramCheck2_23
public import ThreeCopyQutritWerner.CertificateDescendantGramCheck2_24
public import ThreeCopyQutritWerner.CertificateDescendantGramCheck2_25
public import ThreeCopyQutritWerner.CertificateDescendantGramCheck2_26
public import ThreeCopyQutritWerner.CertificateDescendantGramCheck2_27
public import ThreeCopyQutritWerner.CertificateDescendantGramCheck2_28
public import ThreeCopyQutritWerner.CertificateDescendantGramCheck2_29
public import ThreeCopyQutritWerner.CertificateDescendantGramCheck2_30
public import ThreeCopyQutritWerner.CertificateDescendantGramCheck2_31
public import ThreeCopyQutritWerner.CertificateDescendantGramCheck2_32

@[expose] public section


/-! Exact physical Gram factorization in the original complete-frame basis. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

theorem certificateDescendantGram2_blocks (b : Fin 33) :
    (certificateDescendantMatrices2 b)ᵀ * certificateDescendantMatrices2 b =
      certificateDescendantGram2Metric.submatrix (fun j => certificateDescendantGram2Index ⟨b, j⟩) (fun j => certificateDescendantGram2Index ⟨b, j⟩) := by
  fin_cases b
  · exact certificateDescendantGramBlock2_00
  · exact certificateDescendantGramBlock2_01
  · exact certificateDescendantGramBlock2_02
  · exact certificateDescendantGramBlock2_03
  · exact certificateDescendantGramBlock2_04
  · exact certificateDescendantGramBlock2_05
  · exact certificateDescendantGramBlock2_06
  · exact certificateDescendantGramBlock2_07
  · exact certificateDescendantGramBlock2_08
  · exact certificateDescendantGramBlock2_09
  · exact certificateDescendantGramBlock2_10
  · exact certificateDescendantGramBlock2_11
  · exact certificateDescendantGramBlock2_12
  · exact certificateDescendantGramBlock2_13
  · exact certificateDescendantGramBlock2_14
  · exact certificateDescendantGramBlock2_15
  · exact certificateDescendantGramBlock2_16
  · exact certificateDescendantGramBlock2_17
  · exact certificateDescendantGramBlock2_18
  · exact certificateDescendantGramBlock2_19
  · exact certificateDescendantGramBlock2_20
  · exact certificateDescendantGramBlock2_21
  · exact certificateDescendantGramBlock2_22
  · exact certificateDescendantGramBlock2_23
  · exact certificateDescendantGramBlock2_24
  · exact certificateDescendantGramBlock2_25
  · exact certificateDescendantGramBlock2_26
  · exact certificateDescendantGramBlock2_27
  · exact certificateDescendantGramBlock2_28
  · exact certificateDescendantGramBlock2_29
  · exact certificateDescendantGramBlock2_30
  · exact certificateDescendantGramBlock2_31
  · exact certificateDescendantGramBlock2_32

theorem certificateDescendantGram2_weight_metric :
    Matrix.blockDiagonal' (fun b => (certificateDescendantMatrices2 b)ᵀ * certificateDescendantMatrices2 b) =
      certificateDescendantGram2Metric.submatrix certificateDescendantGram2Index certificateDescendantGram2Index := by
  ext ⟨b, i⟩ ⟨c, j⟩
  by_cases h : b = c
  · subst c
    rw [Matrix.blockDiagonal'_apply_eq]
    exact congrFun (congrFun (certificateDescendantGram2_blocks b) i) j
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ h]
    symm
    apply certificateRepeatedFrameMetric_zero
    apply certificateDescendantGram2K_off_weight
    rw [certificateDescendantGram2Weight_index, certificateDescendantGram2Weight_index]
    exact h

/-- The literal full physical descendant Gram, including every cross-type zero. -/
theorem certificateDescendantGram2_physical :
    certificateDescendantFrames2Matrixᵀ * certificateDescendantFrames2Matrix = certificateDescendantGram2Metric := by
  apply certificateGram_of_columns certificateDescendantFrames2Matrix certificateDescendantPhysical2
    certificateDescendantGram2Index certificateDescendantGram2Index_surjective
    (Matrix.ext certificateDescendantFrames2Matrix_bound)
  rw [certificateGram_of_weight_blocks certificateDescendantSizes2
    certificateDescendantRow2 certificateDescendantRow2_bijective _ _
    certificateDescendantPhysical2_blocks]
  exact certificateDescendantGram2_weight_metric

end ThreeCopyQutritWerner
