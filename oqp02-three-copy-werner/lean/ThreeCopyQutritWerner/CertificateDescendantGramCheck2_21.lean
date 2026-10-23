module

public import ThreeCopyQutritWerner.CertificateDescendantGramData2

@[expose] public section


/-! Exact small Gram block for physical weight [0, -4, 0]. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

theorem certificateDescendantGramBlock2_21 :
    certificateDescendantBlockA2_21ᵀ * certificateDescendantBlockA2_21 =
      certificateDescendantGram2Metric.submatrix (fun j : Fin 11 => certificateDescendantGram2Index ⟨21, j⟩)
        (fun j : Fin 11 => certificateDescendantGram2Index ⟨21, j⟩) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
