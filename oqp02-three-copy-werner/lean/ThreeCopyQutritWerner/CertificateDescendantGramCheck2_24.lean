module

public import ThreeCopyQutritWerner.CertificateDescendantGramData2

@[expose] public section


/-! Exact small Gram block for physical weight [0, -1, -3]. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

theorem certificateDescendantGramBlock2_24 :
    certificateDescendantBlockA2_24ᵀ * certificateDescendantBlockA2_24 =
      certificateDescendantGram2Metric.submatrix (fun j : Fin 35 => certificateDescendantGram2Index ⟨24, j⟩)
        (fun j : Fin 35 => certificateDescendantGram2Index ⟨24, j⟩) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
