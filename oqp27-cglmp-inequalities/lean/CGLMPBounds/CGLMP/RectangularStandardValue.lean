module

public import CGLMPBounds.CGLMP.FourierAmplify

@[expose] public section


/-! An actual standard amplification in rectangular product coordinates
has the Fourier table. This structural statement needs no Hardy bound. -/

namespace CGLMPBounds
open Matrix
open scoped Kronecker
noncomputable section

theorem tracialTable_of_rectangular_standard {d n k : ℕ} [NeZero d] [NeZero n]
    (P : Fin 4 → ZMod d → Matrix (Fin n) (Fin n) ℂ)
    (U : Matrix (Fin n) (Fin d × Fin k) ℂ)
    (hdim : n = d*k) (hU : Uᴴ * U = 1)
    (hstd : ∀ (t : Fin 4) (a : ZMod d), P t a =
      U * (fourierProjector d t.val a ⊗ₖ (1 : Matrix (Fin k) (Fin k) ℂ)) * Uᴴ) :
    tracialTable ![P 0,P 2] ![P 1,P 3] = fourierTable d := by
  have hk : k ≠ 0 := by
    intro hz
    have h : n = 0 := by simpa only [hz, Nat.mul_zero] using hdim
    exact NeZero.ne n h
  have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  have htrace (t u : Fin 4) (a b : ZMod d) :
      Matrix.trace (P t a * P u b) =
        (k : ℂ) * Matrix.trace (fourierProjector d t.val a * fourierProjector d u.val b) := by
    let X := fourierProjector d t.val a ⊗ₖ (1 : Matrix (Fin k) (Fin k) ℂ)
    let Y := fourierProjector d u.val b ⊗ₖ (1 : Matrix (Fin k) (Fin k) ℂ)
    have hm : (U * X * Uᴴ) * (U * Y * Uᴴ) = U * (X * Y) * Uᴴ := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Uᴴ U, hU, Matrix.one_mul]
    rw [hstd t a, hstd u b]
    change Matrix.trace ((U*X*Uᴴ)*(U*Y*Uᴴ)) = _
    rw [hm, Matrix.trace_mul_cycle, hU, Matrix.one_mul]
    dsimp only [X, Y]
    rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.trace_kronecker,
      Matrix.trace_one, Fintype.card_fin, mul_comm]
  have hnorm (t u : Fin 4) (a b : ZMod d) :
      (Matrix.trace (P t a * P u b)).re / (n : ℝ) =
        (Matrix.trace (fourierProjector d t.val a * fourierProjector d u.val b)).re / d := by
    rw [htrace, hdim, Nat.cast_mul, ← Complex.ofReal_natCast, Complex.re_ofReal_mul,
      mul_comm (d : ℝ) (k : ℝ), mul_div_mul_left _ _ hk']
  funext x y a b
  fin_cases x <;> fin_cases y
  · simpa [tracialTable, fourierTable] using hnorm 0 1 a b
  · simpa [tracialTable, fourierTable] using hnorm 0 3 a b
  · simpa [tracialTable, fourierTable] using hnorm 2 1 a b
  · simpa [tracialTable, fourierTable] using hnorm 2 3 a b

end
end CGLMPBounds
