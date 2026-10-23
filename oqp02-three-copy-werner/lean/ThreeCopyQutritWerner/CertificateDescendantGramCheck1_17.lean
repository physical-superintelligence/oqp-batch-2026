module

public import ThreeCopyQutritWerner.CertificateDescendantGramData1

@[expose] public section


/-! Exact small Gram block for physical weight [0, -1, 1]. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

theorem certificateDescendantGramBlock1_17 :
    certificateDescendantBlockA1_17ᵀ * certificateDescendantBlockA1_17 =
      certificateDescendantGram1Metric.submatrix (fun j : Fin 60 => certificateDescendantGram1Index ⟨17, j⟩)
        (fun j : Fin 60 => certificateDescendantGram1Index ⟨17, j⟩) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
