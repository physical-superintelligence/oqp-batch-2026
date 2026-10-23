module

public import ThreeCopyQutritWerner.CertificateDescendantGramData2

@[expose] public section


/-! Exact small Gram block for physical weight [0, 0, -4]. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

theorem certificateDescendantGramBlock2_25 :
    certificateDescendantBlockA2_25ᵀ * certificateDescendantBlockA2_25 =
      certificateDescendantGram2Metric.submatrix (fun j : Fin 11 => certificateDescendantGram2Index ⟨25, j⟩)
        (fun j : Fin 11 => certificateDescendantGram2Index ⟨25, j⟩) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
