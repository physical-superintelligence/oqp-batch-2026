module

public import ThreeCopyQutritWerner.CertificateDescendantGramData1

@[expose] public section


/-! Exact small Gram block for physical weight [-1, -1, 2]. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

theorem certificateDescendantGramBlock1_10 :
    certificateDescendantBlockA1_10ᵀ * certificateDescendantBlockA1_10 =
      certificateDescendantGram1Metric.submatrix (fun j : Fin 24 => certificateDescendantGram1Index ⟨10, j⟩)
        (fun j : Fin 24 => certificateDescendantGram1Index ⟨10, j⟩) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
