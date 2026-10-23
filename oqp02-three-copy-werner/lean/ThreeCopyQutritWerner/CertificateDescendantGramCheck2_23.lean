module

public import ThreeCopyQutritWerner.CertificateDescendantGramData2

@[expose] public section


/-! Exact small Gram block for physical weight [0, -2, -2]. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

theorem certificateDescendantGramBlock2_23 :
    certificateDescendantBlockA2_23ᵀ * certificateDescendantBlockA2_23 =
      certificateDescendantGram2Metric.submatrix (fun j : Fin 50 => certificateDescendantGram2Index ⟨23, j⟩)
        (fun j : Fin 50 => certificateDescendantGram2Index ⟨23, j⟩) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
