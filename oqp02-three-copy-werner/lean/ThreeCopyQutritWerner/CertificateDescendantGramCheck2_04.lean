module

public import ThreeCopyQutritWerner.CertificateDescendantGramData2

@[expose] public section


/-! Exact small Gram block for physical weight [-4, 1, -1]. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

theorem certificateDescendantGramBlock2_04 :
    certificateDescendantBlockA2_04ᵀ * certificateDescendantBlockA2_04 =
      certificateDescendantGram2Metric.submatrix (fun j : Fin 5 => certificateDescendantGram2Index ⟨4, j⟩)
        (fun j : Fin 5 => certificateDescendantGram2Index ⟨4, j⟩) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
