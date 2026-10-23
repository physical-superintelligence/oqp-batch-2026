module

public import ThreeCopyQutritWerner.CertificateDescendantGramData1

@[expose] public section


/-! Exact small Gram block for physical weight [0, 3, -3]. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

theorem certificateDescendantGramBlock1_21 :
    certificateDescendantBlockA1_21ᵀ * certificateDescendantBlockA1_21 =
      certificateDescendantGram1Metric.submatrix (fun j : Fin 1 => certificateDescendantGram1Index ⟨21, j⟩)
        (fun j : Fin 1 => certificateDescendantGram1Index ⟨21, j⟩) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
