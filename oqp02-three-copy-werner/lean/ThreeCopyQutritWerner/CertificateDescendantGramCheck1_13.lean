module

public import ThreeCopyQutritWerner.CertificateDescendantGramData1

@[expose] public section


/-! Exact small Gram block for physical weight [-1, 2, -1]. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

theorem certificateDescendantGramBlock1_13 :
    certificateDescendantBlockA1_13ᵀ * certificateDescendantBlockA1_13 =
      certificateDescendantGram1Metric.submatrix (fun j : Fin 24 => certificateDescendantGram1Index ⟨13, j⟩)
        (fun j : Fin 24 => certificateDescendantGram1Index ⟨13, j⟩) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
