module

public import CGLMPBounds.CGLMP.ConditionalMatrixHardyBell
public import CGLMPBounds.Hardy.MatrixHardy

@[expose] public section


/-! Theorem A.1 (bound and equality case) without hypotheses, using the general
matrix Hardy bound C.6 proved in `Hardy/MatrixHardy.lean`. -/
namespace CGLMPBounds
open MeasureTheory Matrix
open scoped Kronecker
noncomputable section

theorem cglmp_projective_bound {d n : ℕ}
    [NeZero d] [NeZero n] (hd : 2 ≤ d)
    (P : Fin 4 → ZMod d → Matrix (Fin n) (Fin n) ℂ) (hP : ∀ t, IsPVM (P t)) :
    cglmp d (tracialTable ![P 0,P 2] ![P 1,P 3]) ≤ cglmpFourierValue d :=
  cglmp_projective_bound_of_matrixHardy_input
    (fun {_} => Hardy.fourth_root_matrix_Hardy_bound) hd P hP

theorem cglmp_eq_fourier_iff_standard {d n : ℕ}
    [NeZero d] [NeZero n] (hd : 2 ≤ d)
    (P : Fin 4 → ZMod d → Matrix (Fin n) (Fin n) ℂ) (hP : ∀ t, IsPVM (P t)) :
    cglmp d (tracialTable ![P 0,P 2] ![P 1,P 3]) = cglmpFourierValue d ↔
      ∃ (k : ℕ) (U : Matrix (Fin n) (Fin d × Fin k) ℂ),
        n = d*k ∧ U*Uᴴ=1 ∧ Uᴴ*U=1 ∧
        ∀ (t : Fin 4) (a : ZMod d), P t a =
          U * (fourierProjector d t.val a ⊗ₖ (1 : Matrix (Fin k) (Fin k) ℂ)) * Uᴴ :=
  cglmp_eq_fourier_iff_standard_of_matrixHardy_input
    (fun {_} => Hardy.fourth_root_matrix_Hardy_bound) hd P hP

end
end CGLMPBounds
