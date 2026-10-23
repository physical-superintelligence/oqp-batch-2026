module

public import ThreeCopyQutritWerner.CertificateDescendantGramData1

@[expose] public section


/-! Exact small Gram block for physical weight [2, 0, -2]. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

theorem certificateDescendantGramBlock1_31 :
    certificateDescendantBlockA1_31ᵀ * certificateDescendantBlockA1_31 =
      certificateDescendantGram1Metric.submatrix (fun j : Fin 15 => certificateDescendantGram1Index ⟨31, j⟩)
        (fun j : Fin 15 => certificateDescendantGram1Index ⟨31, j⟩) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
