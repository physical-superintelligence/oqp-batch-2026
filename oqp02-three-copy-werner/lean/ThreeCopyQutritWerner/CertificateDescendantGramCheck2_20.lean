module

public import ThreeCopyQutritWerner.CertificateDescendantGramData2

@[expose] public section


/-! Exact small Gram block for physical weight [0, -5, 1]. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

theorem certificateDescendantGramBlock2_20 :
    certificateDescendantBlockA2_20ᵀ * certificateDescendantBlockA2_20 =
      certificateDescendantGram2Metric.submatrix (fun j : Fin 1 => certificateDescendantGram2Index ⟨20, j⟩)
        (fun j : Fin 1 => certificateDescendantGram2Index ⟨20, j⟩) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
