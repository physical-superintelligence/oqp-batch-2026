module

public import ThreeCopyQutritWerner.CertificateDescendantGramData2

@[expose] public section


/-! Exact small Gram block for physical weight [1, -2, -3]. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

theorem certificateDescendantGramBlock2_30 :
    certificateDescendantBlockA2_30ᵀ * certificateDescendantBlockA2_30 =
      certificateDescendantGram2Metric.submatrix (fun j : Fin 10 => certificateDescendantGram2Index ⟨30, j⟩)
        (fun j : Fin 10 => certificateDescendantGram2Index ⟨30, j⟩) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
