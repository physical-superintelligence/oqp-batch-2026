module

public import ThreeCopyQutritWerner.CertificateDescendantGramData2

@[expose] public section


/-! Exact small Gram block for physical weight [1, -5, 0]. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

theorem certificateDescendantGramBlock2_27 :
    certificateDescendantBlockA2_27ᵀ * certificateDescendantBlockA2_27 =
      certificateDescendantGram2Metric.submatrix (fun j : Fin 1 => certificateDescendantGram2Index ⟨27, j⟩)
        (fun j : Fin 1 => certificateDescendantGram2Index ⟨27, j⟩) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
