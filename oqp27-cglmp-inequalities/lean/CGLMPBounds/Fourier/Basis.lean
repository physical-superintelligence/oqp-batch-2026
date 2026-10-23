module

public import CGLMPBounds.Fourier.Entries
public import CGLMPBounds.Quantum.Tracial

@[expose] public section


/-!
# The Fourier-phase measurements are projective measurements

* `inner_fourierVector_same` : `⟨ψ_{t,a}|ψ_{t,b}⟩ = δ_{ab}` (orthonormality, by geometric sums);
* `sum_fourierProjector` : `Σ_a Π^t_a = 1` (completeness: `UᴴU = 1` forces `UUᴴ = 1`);
* `fourierProjector_isPVM` : each `{Π^t_a}_a` is a projective measurement;
* `fourierTable_isNoSignalling`, `sum_fourierTable_right`, `sum_fourierTable_left` :
  `Q_d` is a no-signalling behaviour with uniform marginals.
-/

namespace CGLMPBounds

open Matrix

noncomputable section

variable (d : ℕ) [NeZero d]

theorem fourierAngle_same (t : ℕ) (a b : ZMod d) :
    fourierAngle d t t a b = 2 * Real.pi * ((a.val : ℝ) - b.val) / d := by
  unfold fourierAngle
  ring

/-- Orthonormality of the Fourier-phase basis `{ψ_{t,a}}_a`. -/
theorem inner_fourierVector_same (t : ℕ) (a b : ZMod d) :
    star (fourierVector d t a) ⬝ᵥ fourierVector d t b = if a = b then 1 else 0 := by
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  rw [inner_fourierVector, sum_exp_mul_I, fourierAngle_same]
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl]
    simp only [sub_self, mul_zero, zero_div, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
      one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_mul, one_div_mul_cancel hd0, Complex.ofReal_one]
  · rw [if_neg hab]
    have hm0 : (a.val : ℤ) - b.val ≠ 0 := by
      intro h
      apply hab
      apply ZMod.val_injective
      omega
    have hmd : |(a.val : ℤ) - b.val| < d := by
      have ha := ZMod.val_lt a
      have hb := ZMod.val_lt b
      rw [abs_lt]
      constructor <;> omega
    set β := 2 * Real.pi * ((a.val : ℝ) - b.val) / d with hβdef
    have hsin : Real.sin (β / 2) ≠ 0 := by
      intro h
      obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp h
      have h2 : β / 2 = Real.pi * ((a.val : ℝ) - b.val) / d := by
        rw [hβdef]
        ring
      rw [h2, eq_div_iff hd0] at hn
      have hn' : (n : ℝ) * d = (a.val : ℝ) - b.val :=
        mul_right_cancel₀ Real.pi_ne_zero (by linarith)
      have hz : n * (d : ℤ) = (a.val : ℤ) - b.val := by exact_mod_cast hn'
      have hd' : (0 : ℤ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
      obtain ⟨hlo, hhi⟩ := abs_lt.mp hmd
      rcases lt_trichotomy n 0 with h1 | h1 | h1
      · nlinarith
      · rw [h1, zero_mul] at hz
        exact hm0 hz.symm
      · nlinarith
    have hw1 : Complex.exp ((β : ℂ) * Complex.I) ≠ 1 := by
      intro h
      have h4 := normSq_exp_mul_I_sub_one β
      rw [h, sub_self, Complex.normSq_zero] at h4
      have hs : 0 < Real.sin (β / 2) ^ 2 :=
        lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hsin))
      linarith
    have hwd : Complex.exp ((β : ℂ) * Complex.I) ^ d = 1 := by
      rw [← Complex.exp_nat_mul]
      have e : (d : ℂ) * ((β : ℂ) * Complex.I)
          = (((a.val : ℤ) - b.val : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
        rw [hβdef]
        push_cast
        calc (d : ℂ) * (2 * Real.pi * ((a.val : ℂ) - b.val) / d * Complex.I)
            = ((d : ℂ) / d) * (((a.val : ℂ) - b.val) * (2 * Real.pi * Complex.I)) := by ring
          _ = ((a.val : ℂ) - b.val) * (2 * Real.pi * Complex.I) := by rw [div_self hdC, one_mul]
      rw [e, Complex.exp_int_mul_two_pi_mul_I]
    rw [geom_sum_eq hw1, hwd, sub_self, zero_div, mul_zero]

/-- Completeness of the Fourier-phase basis: `Σ_a Π^t_a = 1`. -/
theorem sum_fourierProjector (t : ℕ) : ∑ a : ZMod d, fourierProjector d t a = 1 := by
  let U : Matrix (Fin d) (ZMod d) ℂ := Matrix.of fun j a => fourierVector d t a j
  have hUU : Uᴴ * U = 1 := by
    ext a b
    rw [Matrix.mul_apply, Matrix.one_apply, ← inner_fourierVector_same d t a b]
    rfl
  have hUU' : U * Uᴴ = 1 :=
    (Matrix.mul_eq_one_comm_of_equiv (Fintype.equivOfCardEq (by simp [ZMod.card]))).mp hUU
  ext i j
  rw [Matrix.sum_apply, ← hUU', Matrix.mul_apply]
  rfl

/-- The Fourier-phase projectors `{Π^t_a}_a` form a projective measurement. -/
theorem fourierProjector_isPVM (t : ℕ) : IsPVM (fourierProjector d t) where
  isHermitian a := by
    unfold fourierProjector Matrix.IsHermitian
    rw [conjTranspose_vecMulVec, star_star]
  mul_self a := by
    unfold fourierProjector
    rw [vecMulVec_mul_vecMulVec, inner_fourierVector_same, if_pos rfl, one_smul]
  sum_eq_one := sum_fourierProjector d t

theorem re_trace_fourierProjector (t : ℕ) (a : ZMod d) :
    (trace (fourierProjector d t a)).re = 1 := by
  unfold fourierProjector
  rw [trace_vecMulVec, dotProduct_comm, inner_fourierVector_same, if_pos rfl, Complex.one_re]

/-- The Fourier-phase behaviour `Q_d` is a no-signalling behaviour. -/
theorem fourierTable_isNoSignalling : IsNoSignalling (fourierTable d) :=
  tracialTable_isNoSignalling (fun x => fourierProjector_isPVM d _)
    (fun y => fourierProjector_isPVM d _)

/-- Alice's marginal of `Q_d` is uniform. -/
theorem sum_fourierTable_right (x y : Fin 2) (a : ZMod d) :
    ∑ b : ZMod d, fourierTable d x y a b = 1 / (d : ℝ) := by
  show ∑ b : ZMod d, (trace (fourierProjector d (2 * x.val) a
    * fourierProjector d (1 + 2 * y.val) b)).re / (d : ℝ) = 1 / (d : ℝ)
  rw [← Finset.sum_div, sum_right_re_trace_mul (fourierProjector_isPVM d _).sum_eq_one,
    re_trace_fourierProjector]

/-- Bob's marginal of `Q_d` is uniform. -/
theorem sum_fourierTable_left (x y : Fin 2) (b : ZMod d) :
    ∑ a : ZMod d, fourierTable d x y a b = 1 / (d : ℝ) := by
  show ∑ a : ZMod d, (trace (fourierProjector d (2 * x.val) a
    * fourierProjector d (1 + 2 * y.val) b)).re / (d : ℝ) = 1 / (d : ℝ)
  rw [← Finset.sum_div, sum_left_re_trace_mul (fourierProjector_isPVM d _).sum_eq_one,
    re_trace_fourierProjector]

end

end CGLMPBounds
