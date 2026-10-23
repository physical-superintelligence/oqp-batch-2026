module

public import ThreeCopyQutritWerner.CertificateDescendantGramData1

@[expose] public section


/-! Exact small Gram block for physical weight [0, 1, -1]. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

theorem certificateDescendantGramBlock1_19 :
    certificateDescendantBlockA1_19ᵀ * certificateDescendantBlockA1_19 =
      certificateDescendantGram1Metric.submatrix (fun j : Fin 60 => certificateDescendantGram1Index ⟨19, j⟩)
        (fun j : Fin 60 => certificateDescendantGram1Index ⟨19, j⟩) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
