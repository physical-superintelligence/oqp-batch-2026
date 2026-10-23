module

public import CGLMPBounds.Companion.Fourier
public import CGLMPBounds.Defs.FourthRootCut

@[expose] public section


/-!
# The scalar cut frequency shift in (E.1)

For s=d−1−j₀ the cut factor −i on j>j₀ is exactly the wrap factor
of the source phase λ_(j+s mod d), after division by λ_s.
-/

namespace CGLMPBounds.Companion
noncomputable section
variable {d : ℕ} [NeZero d]

lemma etaD_pow_dimension : etaD d ^ d = Complex.I := by
  rw [etaD, ← Complex.exp_nat_mul]
  have hd : (d : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne d
  have he : (d : ℂ) * (((Real.pi / (2 * d) : ℝ) : ℂ) * Complex.I) =
      (Real.pi : ℂ) / 2 * Complex.I := by
    push_cast
    field_simp [hd]
    <;> ring
  rw [he, Complex.exp_pi_div_two_mul_I]

/-- The exact phase identity printed directly below the cut formula E.1. -/
theorem sourcePhase_cut_shift (j₀ j : Fin d) :
    let s : Fin d := ⟨d - 1 - j₀.val, by have := j₀.isLt; omega⟩
    sourcePhase j * (if j₀ < j then -Complex.I else 1) =
      (sourcePhase s)⁻¹ * sourcePhase (j + s) := by
  let s : Fin d := ⟨d - 1 - j₀.val, by have := j₀.isLt; omega⟩
  change sourcePhase j * (if j₀ < j then -Complex.I else 1) =
    (sourcePhase s)⁻¹ * sourcePhase (j + s)
  have hs : s.val = d - 1 - j₀.val := rfl
  have hjlt := j.isLt
  have hj₀lt := j₀.isLt
  apply mul_left_cancel₀ (sourcePhase_ne_zero s)
  rw [← mul_assoc (sourcePhase s) (sourcePhase s)⁻¹,
    mul_inv_cancel₀ (sourcePhase_ne_zero s), one_mul]
  by_cases hj : j₀ < j
  · rw [if_pos hj]
    have hwrap : d ≤ j.val + s.val := by
      have hj' : j₀.val < j.val := hj
      omega
    have hval : (j + s).val = j.val + s.val - d := by
      rw [Fin.val_add_eq_ite, if_pos hwrap]
    have hexp : d + (j.val + s.val - d) = j.val + s.val := by omega
    calc
      sourcePhase s * (sourcePhase j * -Complex.I) =
          etaD d ^ (j.val + s.val) * -Complex.I := by
        rw [sourcePhase, sourcePhase, pow_add]
        ring
      _ = (etaD d ^ d * etaD d ^ (j.val + s.val - d)) * -Complex.I := by
        rw [← pow_add, hexp]
      _ = sourcePhase (j + s) := by
        rw [etaD_pow_dimension, sourcePhase, hval]
        have hi := Complex.I_sq
        ring_nf at hi ⊢
        simp [hi]
  · rw [if_neg hj, mul_one]
    have hnowrap : j.val + s.val < d := by
      have hj' : ¬ j₀.val < j.val := hj
      omega
    rw [sourcePhase, sourcePhase, sourcePhase, Fin.val_add_eq_of_add_lt hnowrap, pow_add]
    exact mul_comm _ _

end
end CGLMPBounds.Companion
