module

public import ThreeCopyQutritWerner.CertificateDescendantGramData2

@[expose] public section


/-! Exact small Gram block for physical weight [-3, -2, 1]. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

theorem certificateDescendantGramBlock2_05 :
    certificateDescendantBlockA2_05ᵀ * certificateDescendantBlockA2_05 =
      certificateDescendantGram2Metric.submatrix (fun j : Fin 10 => certificateDescendantGram2Index ⟨5, j⟩)
        (fun j : Fin 10 => certificateDescendantGram2Index ⟨5, j⟩) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
