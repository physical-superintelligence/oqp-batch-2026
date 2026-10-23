module

public import ThreeCopyQutritWerner.CertificateDescendantGramData1

@[expose] public section


/-! Exact small Gram block for physical weight [1, -1, 0]. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

theorem certificateDescendantGramBlock1_24 :
    certificateDescendantBlockA1_24ᵀ * certificateDescendantBlockA1_24 =
      certificateDescendantGram1Metric.submatrix (fun j : Fin 60 => certificateDescendantGram1Index ⟨24, j⟩)
        (fun j : Fin 60 => certificateDescendantGram1Index ⟨24, j⟩) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
