module

public import ThreeCopyQutritWerner.CertificateDescendantGramData1

@[expose] public section


/-! Exact small Gram block for physical weight [3, -3, 0]. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

theorem certificateDescendantGramBlock1_33 :
    certificateDescendantBlockA1_33ᵀ * certificateDescendantBlockA1_33 =
      certificateDescendantGram1Metric.submatrix (fun j : Fin 1 => certificateDescendantGram1Index ⟨33, j⟩)
        (fun j : Fin 1 => certificateDescendantGram1Index ⟨33, j⟩) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
