module

public import ThreeCopyQutritWerner.CertificateDescendantGramData1

@[expose] public section


/-! Exact small Gram block for physical weight [0, -3, 3]. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

theorem certificateDescendantGramBlock1_15 :
    certificateDescendantBlockA1_15ᵀ * certificateDescendantBlockA1_15 =
      certificateDescendantGram1Metric.submatrix (fun j : Fin 1 => certificateDescendantGram1Index ⟨15, j⟩)
        (fun j : Fin 1 => certificateDescendantGram1Index ⟨15, j⟩) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
