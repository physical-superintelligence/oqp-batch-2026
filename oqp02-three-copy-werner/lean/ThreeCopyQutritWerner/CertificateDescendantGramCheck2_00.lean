module

public import ThreeCopyQutritWerner.CertificateDescendantGramData2

@[expose] public section


/-! Exact small Gram block for physical weight [-5, 0, 1]. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

theorem certificateDescendantGramBlock2_00 :
    certificateDescendantBlockA2_00ᵀ * certificateDescendantBlockA2_00 =
      certificateDescendantGram2Metric.submatrix (fun j : Fin 1 => certificateDescendantGram2Index ⟨0, j⟩)
        (fun j : Fin 1 => certificateDescendantGram2Index ⟨0, j⟩) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
