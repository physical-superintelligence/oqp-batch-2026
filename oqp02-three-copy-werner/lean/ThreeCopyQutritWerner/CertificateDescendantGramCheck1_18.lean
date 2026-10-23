module

public import ThreeCopyQutritWerner.CertificateDescendantGramData1

@[expose] public section


/-! Exact small Gram block for physical weight [0, 0, 0]. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

theorem certificateDescendantGramBlock1_18 :
    certificateDescendantBlockA1_18ᵀ * certificateDescendantBlockA1_18 =
      certificateDescendantGram1Metric.submatrix (fun j : Fin 93 => certificateDescendantGram1Index ⟨18, j⟩)
        (fun j : Fin 93 => certificateDescendantGram1Index ⟨18, j⟩) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
