module

public import ThreeCopyQutritWerner.CertificateDescendantGramData1

@[expose] public section


/-! Exact small Gram block for physical weight [0, 2, -2]. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

theorem certificateDescendantGramBlock1_20 :
    certificateDescendantBlockA1_20ᵀ * certificateDescendantBlockA1_20 =
      certificateDescendantGram1Metric.submatrix (fun j : Fin 15 => certificateDescendantGram1Index ⟨20, j⟩)
        (fun j : Fin 15 => certificateDescendantGram1Index ⟨20, j⟩) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
