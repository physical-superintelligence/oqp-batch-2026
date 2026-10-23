module

public import CGLMPBounds.Defs.Fourier
public import CGLMPBounds.CGLMP.LocalBound
public import CGLMPBounds.Fourier.LocalWeight

@[expose] public section


/-!
# Entries of the Fourier-phase behaviour: equation (F.1)

Supplement, Appendix F.1: "Geometric summation of (B.2) gives
`Q_d(a,b|x,y) = f_d(r_{xy})/d`, `f_d(r) = 1/(2d² sin²(π(r + 1/4)/d))`."

Route: `Tr(Π^s_a Π^t_b) = |⟨ψ_{s,a}|ψ_{t,b}⟩|²`; the inner product is `d⁻¹ Σ_j e^{ijβ}` with
`β = 2π(a - b - (s-t)/4)/d`; `|Σ_{j<d} e^{ijβ}|² = sin²(dβ/2)/sin²(β/2)`; for the four contexts
`sin²(dβ/2) = 1/2` and `sin²(β/2) = sin²(π(r_{xy} + 1/4)/d)`.

* `fourierTable_apply` : `Q_d(a,b|x,y) = f_d(r_{xy}(a,b)) / d` for `d ≥ 2`.
-/

namespace CGLMPBounds

open Matrix

noncomputable section

/-! ### Rank-one projectors -/

/-- `Tr(|u⟩⟨u| |v⟩⟨v|) = |⟨u|v⟩|²`. -/
theorem re_trace_vecMulVec_star_mul {n : ℕ} (u v : Fin n → ℂ) :
    (trace (vecMulVec u (star u) * vecMulVec v (star v))).re = Complex.normSq (star u ⬝ᵥ v) := by
  rw [vecMulVec_mul_vecMulVec, trace_vecMulVec, dotProduct_smul, smul_eq_mul, dotProduct_star,
    dotProduct_comm v (star u), ← starRingEnd_apply (star u ⬝ᵥ v), Complex.mul_conj,
    Complex.ofReal_re]

/-! ### Phases and inner products -/

/-- The phase of `ψ_{t,a}(j)`: `ψ_{t,a}(j) = d^{-1/2} e^{iφ}`. -/
def fourierPhase (d t : ℕ) (a : ZMod d) (j : ℕ) : ℝ :=
  -(2 * Real.pi * j * ((a.val : ℝ) - t / 4) / d)

theorem fourierVector_eq (d t : ℕ) (a : ZMod d) (j : Fin d) :
    fourierVector d t a j
      = (((Real.sqrt d)⁻¹ : ℝ) : ℂ) * Complex.exp ((fourierPhase d t a j : ℂ) * Complex.I) := by
  unfold fourierVector fourierPhase
  congr 2
  push_cast
  ring

theorem star_exp_ofReal_mul_I (θ : ℝ) :
    star (Complex.exp ((θ : ℂ) * Complex.I)) = Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) := by
  rw [← starRingEnd_apply (Complex.exp ((θ : ℂ) * Complex.I)), ← Complex.exp_conj, map_mul,
    Complex.conj_ofReal, Complex.conj_I]
  congr 1
  push_cast
  ring

/-- The relative angle `β = 2π (a - b - (s - t)/4)/d` of `⟨ψ_{s,a}|ψ_{t,b}⟩`. -/
def fourierAngle (d s t : ℕ) (a b : ZMod d) : ℝ :=
  2 * Real.pi * ((a.val : ℝ) - b.val - ((s : ℝ) - t) / 4) / d

/-- `⟨ψ_{s,a}|ψ_{t,b}⟩ = d⁻¹ Σ_j e^{ijβ}`. -/
theorem inner_fourierVector (d s t : ℕ) (a b : ZMod d) :
    star (fourierVector d s a) ⬝ᵥ fourierVector d t b
      = ((1 / (d : ℝ) : ℝ) : ℂ) * ∑ j : Fin d,
          Complex.exp ((((j : ℕ) : ℝ) * fourierAngle d s t a b : ℝ) * Complex.I) := by
  rw [Finset.mul_sum]
  simp only [dotProduct, Pi.star_apply, fourierVector_eq]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hsc : (((Real.sqrt d)⁻¹ : ℝ) : ℂ) * (((Real.sqrt d)⁻¹ : ℝ) : ℂ)
      = ((1 / (d : ℝ) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg d), one_div]
  have hexp : Complex.exp (((-fourierPhase d s a j : ℝ) : ℂ) * Complex.I)
        * Complex.exp ((fourierPhase d t b j : ℂ) * Complex.I)
      = Complex.exp ((((j : ℕ) : ℝ) * fourierAngle d s t a b : ℝ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    unfold fourierPhase fourierAngle
    push_cast
    ring
  rw [star_mul', ← starRingEnd_apply ((((Real.sqrt d)⁻¹ : ℝ) : ℂ)), Complex.conj_ofReal,
    star_exp_ofReal_mul_I, mul_mul_mul_comm, hsc, hexp]

/-! ### Geometric sums -/

theorem sum_exp_mul_I (d : ℕ) (β : ℝ) :
    ∑ j : Fin d, Complex.exp ((((j : ℕ) : ℝ) * β : ℝ) * Complex.I)
      = ∑ j ∈ Finset.range d, Complex.exp ((β : ℂ) * Complex.I) ^ j := by
  rw [Fin.sum_univ_eq_sum_range (fun j => Complex.exp ((((j : ℕ) : ℝ) * β : ℝ) * Complex.I)) d]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem normSq_exp_mul_I_sub_one (x : ℝ) :
    Complex.normSq (Complex.exp ((x : ℂ) * Complex.I) - 1) = 4 * Real.sin (x / 2) ^ 2 := by
  rw [Complex.normSq_eq_norm_sq, mul_comm (x : ℂ) Complex.I, Complex.norm_exp_I_mul_ofReal_sub_one,
    Real.norm_eq_abs, sq_abs]
  ring

/-- `|Σ_{j<d} e^{ijβ}|² = sin²(dβ/2) / sin²(β/2)` when `sin(β/2) ≠ 0`. -/
theorem normSq_geom_exp (d : ℕ) (β : ℝ) (hβ : Real.sin (β / 2) ≠ 0) :
    Complex.normSq (∑ j ∈ Finset.range d, Complex.exp ((β : ℂ) * Complex.I) ^ j)
      = Real.sin (d * β / 2) ^ 2 / Real.sin (β / 2) ^ 2 := by
  have hw1 : Complex.exp ((β : ℂ) * Complex.I) ≠ 1 := by
    intro h
    have h4 := normSq_exp_mul_I_sub_one β
    rw [h, sub_self, Complex.normSq_zero] at h4
    have hs : 0 < Real.sin (β / 2) ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hβ))
    linarith
  have hpow : Complex.exp ((β : ℂ) * Complex.I) ^ d
      = Complex.exp ((((d : ℝ) * β : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [geom_sum_eq hw1, Complex.normSq_div, hpow, normSq_exp_mul_I_sub_one,
    normSq_exp_mul_I_sub_one, mul_div_mul_left _ _ (by norm_num : (4 : ℝ) ≠ 0)]

/-! ### Trigonometric values -/

theorem sin_sq_add_int_mul_pi (x : ℝ) (n : ℤ) :
    Real.sin (x + n * Real.pi) ^ 2 = Real.sin x ^ 2 := by
  rw [Real.sin_add_int_mul_pi]
  rcases Int.even_or_odd n with h | h
  · rw [h.neg_one_zpow, one_mul]
  · rw [h.neg_one_zpow, neg_one_mul, neg_sq]

theorem sin_sq_pi_div_four : Real.sin (Real.pi / 4) ^ 2 = 1 / 2 := by
  rw [Real.sin_pi_div_four, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

theorem sin_sq_neg_pi_div_four : Real.sin (-(Real.pi / 4)) ^ 2 = 1 / 2 := by
  rw [Real.sin_neg, neg_sq, sin_sq_pi_div_four]

theorem sin_sq_three_pi_div_four : Real.sin (Real.pi - Real.pi / 4) ^ 2 = 1 / 2 := by
  rw [Real.sin_pi_sub, sin_sq_pi_div_four]

theorem mul_fourierAngle_div_two (d s t : ℕ) [NeZero d] (a b : ZMod d) :
    (d : ℝ) * fourierAngle d s t a b / 2
      = Real.pi * ((a.val : ℝ) - b.val - ((s : ℝ) - t) / 4) := by
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  unfold fourierAngle
  calc (d : ℝ) * (2 * Real.pi * ((a.val : ℝ) - b.val - ((s : ℝ) - t) / 4) / d) / 2
      = ((d : ℝ) / d) * (Real.pi * ((a.val : ℝ) - b.val - ((s : ℝ) - t) / 4)) := by ring
    _ = Real.pi * ((a.val : ℝ) - b.val - ((s : ℝ) - t) / 4) := by rw [div_self hd0, one_mul]

theorem fourierAngle_div_two (d s t : ℕ) (a b : ZMod d) :
    fourierAngle d s t a b / 2 = Real.pi * ((a.val : ℝ) - b.val - ((s : ℝ) - t) / 4) / d := by
  unfold fourierAngle
  ring

/-! ### Residues modulo `d` -/

/-- An integer representing `u ∈ ℤ_d` differs from `u.val` by a multiple of `d`. -/
theorem exists_val_eq (d : ℕ) [NeZero d] (u : ZMod d) (Y : ℤ) (hY : ((Y : ℤ) : ZMod d) = u) :
    ∃ k : ℤ, ((u.val : ℕ) : ℝ) = (Y : ℝ) + d * k := by
  have h : (((u.val : ℕ) : ℤ) : ZMod d) = ((Y : ℤ) : ZMod d) := by
    rw [Int.cast_natCast, ZMod.natCast_zmod_val, hY]
  obtain ⟨k, hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ d).mp h
  refine ⟨-k, ?_⟩
  have hk' : (((Y - ((u.val : ℕ) : ℤ)) : ℤ) : ℝ) = (((d : ℤ) * k : ℤ) : ℝ) := by rw [hk]
  push_cast at hk' ⊢
  linarith

theorem pi_mul_add_div (d : ℕ) [NeZero d] (X : ℝ) (k : ℤ) :
    Real.pi * (X + d * k) / d = Real.pi * X / d + (k : ℝ) * Real.pi := by
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  calc Real.pi * (X + d * k) / d = Real.pi * X / d + ((d : ℝ) / d) * ((k : ℝ) * Real.pi) := by
        ring
    _ = Real.pi * X / d + (k : ℝ) * Real.pi := by rw [div_self hd0, one_mul]

/-! ### Assembly -/

/-- If `sin²(dβ/2) = 1/2` and `sin²(β/2) = sin²(π(r + 1/4)/d)` with `r < d`, then
`Tr(Π^s_a Π^t_b)/d = f_d(r)/d`. -/
theorem trace_fourierProjector_eq (d : ℕ) [NeZero d] (s t : ℕ) (a b : ZMod d) (r : ℕ)
    (hr : r < d)
    (h1 : Real.sin (d * fourierAngle d s t a b / 2) ^ 2 = 1 / 2)
    (h2 : Real.sin (fourierAngle d s t a b / 2) ^ 2
      = Real.sin (Real.pi * ((r : ℝ) + 1 / 4) / d) ^ 2) :
    (trace (fourierProjector d s a * fourierProjector d t b)).re / d
      = fourierResidualLaw d r / d := by
  have hd0 : (0 : ℝ) < d := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne d))
  have hr' : (r : ℝ) + 1 / 4 < d := by
    have : (r : ℝ) + 1 ≤ d := by exact_mod_cast hr
    linarith
  have hpos : 0 < Real.sin (Real.pi * ((r : ℝ) + 1 / 4) / d) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · exact div_pos (mul_pos Real.pi_pos (by positivity)) hd0
    · rw [div_lt_iff₀ hd0]
      exact mul_lt_mul_of_pos_left hr' Real.pi_pos
  have hβ : Real.sin (fourierAngle d s t a b / 2) ≠ 0 := by
    intro h0
    rw [h0, zero_pow two_ne_zero] at h2
    linarith [pow_pos hpos 2]
  unfold fourierProjector
  rw [re_trace_vecMulVec_star_mul, inner_fourierVector, Complex.normSq_mul, Complex.normSq_ofReal,
    sum_exp_mul_I, normSq_geom_exp d _ hβ, h1, h2]
  unfold fourierResidualLaw
  ring

/-! ### The four contexts -/

theorem fourierTable_zero_zero (d : ℕ) [NeZero d] (a b : ZMod d) :
    fourierTable d 0 0 a b = fourierResidualLaw d (residual d 0 0 a b) / d := by
  show (trace (fourierProjector d 0 a * fourierProjector d 1 b)).re / d = _
  obtain ⟨k, hk⟩ := exists_val_eq d (a - b) ((a.val : ℤ) - b.val) (by
    rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast, ZMod.natCast_zmod_val,
      ZMod.natCast_zmod_val])
  refine trace_fourierProjector_eq d 0 1 a b _
    (by rw [residual_zero_zero]; exact ZMod.val_lt _) ?_ ?_
  · rw [mul_fourierAngle_div_two,
      show Real.pi * ((a.val : ℝ) - b.val - (((0 : ℕ) : ℝ) - ((1 : ℕ) : ℝ)) / 4)
        = Real.pi / 4 + (((a.val : ℤ) - b.val : ℤ) : ℝ) * Real.pi by push_cast; ring,
      sin_sq_add_int_mul_pi, sin_sq_pi_div_four]
  · rw [residual_zero_zero, hk, fourierAngle_div_two,
      show ((((a.val : ℤ) - b.val : ℤ) : ℝ) + d * k) + 1 / 4
        = ((a.val : ℝ) - b.val - (((0 : ℕ) : ℝ) - ((1 : ℕ) : ℝ)) / 4) + d * k by push_cast; ring,
      pi_mul_add_div, sin_sq_add_int_mul_pi]

theorem fourierTable_one_one (d : ℕ) [NeZero d] (a b : ZMod d) :
    fourierTable d 1 1 a b = fourierResidualLaw d (residual d 1 1 a b) / d := by
  show (trace (fourierProjector d 2 a * fourierProjector d 3 b)).re / d = _
  obtain ⟨k, hk⟩ := exists_val_eq d (a - b) ((a.val : ℤ) - b.val) (by
    rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast, ZMod.natCast_zmod_val,
      ZMod.natCast_zmod_val])
  refine trace_fourierProjector_eq d 2 3 a b _
    (by rw [residual_one_one]; exact ZMod.val_lt _) ?_ ?_
  · rw [mul_fourierAngle_div_two,
      show Real.pi * ((a.val : ℝ) - b.val - (((2 : ℕ) : ℝ) - ((3 : ℕ) : ℝ)) / 4)
        = Real.pi / 4 + (((a.val : ℤ) - b.val : ℤ) : ℝ) * Real.pi by push_cast; ring,
      sin_sq_add_int_mul_pi, sin_sq_pi_div_four]
  · rw [residual_one_one, hk, fourierAngle_div_two,
      show ((((a.val : ℤ) - b.val : ℤ) : ℝ) + d * k) + 1 / 4
        = ((a.val : ℝ) - b.val - (((2 : ℕ) : ℝ) - ((3 : ℕ) : ℝ)) / 4) + d * k by push_cast; ring,
      pi_mul_add_div, sin_sq_add_int_mul_pi]

theorem fourierTable_one_zero (d : ℕ) [NeZero d] (a b : ZMod d) :
    fourierTable d 1 0 a b = fourierResidualLaw d (residual d 1 0 a b) / d := by
  show (trace (fourierProjector d 2 a * fourierProjector d 1 b)).re / d = _
  obtain ⟨k, hk⟩ := exists_val_eq d (b - a) ((b.val : ℤ) - a.val) (by
    rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast, ZMod.natCast_zmod_val,
      ZMod.natCast_zmod_val])
  refine trace_fourierProjector_eq d 2 1 a b _
    (by rw [residual_one_zero]; exact ZMod.val_lt _) ?_ ?_
  · rw [mul_fourierAngle_div_two,
      show Real.pi * ((a.val : ℝ) - b.val - (((2 : ℕ) : ℝ) - ((1 : ℕ) : ℝ)) / 4)
        = -(Real.pi / 4) + (((a.val : ℤ) - b.val : ℤ) : ℝ) * Real.pi by push_cast; ring,
      sin_sq_add_int_mul_pi, sin_sq_neg_pi_div_four]
  · rw [residual_one_zero, hk, fourierAngle_div_two,
      show ((((b.val : ℤ) - a.val : ℤ) : ℝ) + d * k) + 1 / 4
        = ((b.val : ℝ) - a.val + 1 / 4) + d * k by push_cast; ring,
      pi_mul_add_div, sin_sq_add_int_mul_pi,
      show Real.pi * ((a.val : ℝ) - b.val - (((2 : ℕ) : ℝ) - ((1 : ℕ) : ℝ)) / 4) / d
        = -(Real.pi * ((b.val : ℝ) - a.val + 1 / 4) / d) by push_cast; ring,
      Real.sin_neg, neg_sq]

theorem fourierTable_zero_one (d : ℕ) [NeZero d] (a b : ZMod d) :
    fourierTable d 0 1 a b = fourierResidualLaw d (residual d 0 1 a b) / d := by
  show (trace (fourierProjector d 0 a * fourierProjector d 3 b)).re / d = _
  obtain ⟨k, hk⟩ := exists_val_eq d (b - a - 1) ((b.val : ℤ) - a.val - 1) (by
    rw [Int.cast_sub, Int.cast_sub, Int.cast_natCast, Int.cast_natCast, Int.cast_one,
      ZMod.natCast_zmod_val, ZMod.natCast_zmod_val])
  refine trace_fourierProjector_eq d 0 3 a b _
    (by rw [residual_zero_one]; exact ZMod.val_lt _) ?_ ?_
  · rw [mul_fourierAngle_div_two,
      show Real.pi * ((a.val : ℝ) - b.val - (((0 : ℕ) : ℝ) - ((3 : ℕ) : ℝ)) / 4)
        = (Real.pi - Real.pi / 4) + (((a.val : ℤ) - b.val : ℤ) : ℝ) * Real.pi by push_cast; ring,
      sin_sq_add_int_mul_pi, sin_sq_three_pi_div_four]
  · rw [residual_zero_one, hk, fourierAngle_div_two,
      show ((((b.val : ℤ) - a.val - 1 : ℤ) : ℝ) + d * k) + 1 / 4
        = ((b.val : ℝ) - a.val - 1 + 1 / 4) + d * k by push_cast; ring,
      pi_mul_add_div, sin_sq_add_int_mul_pi,
      show Real.pi * ((a.val : ℝ) - b.val - (((0 : ℕ) : ℝ) - ((3 : ℕ) : ℝ)) / 4) / d
        = -(Real.pi * ((b.val : ℝ) - a.val - 1 + 1 / 4) / d) by push_cast; ring,
      Real.sin_neg, neg_sq]

/-- **Equation (F.1).** The Fourier-phase behaviour is `Q_d(a,b|x,y) = f_d(r_{xy}(a,b)) / d`. -/
theorem fourierTable_apply (d : ℕ) [NeZero d] :
    ∀ (x y : Fin 2) (a b : ZMod d),
      fourierTable d x y a b = fourierResidualLaw d (residual d x y a b) / d := by
  refine Fin.forall_fin_two.mpr ⟨Fin.forall_fin_two.mpr ⟨?_, ?_⟩, Fin.forall_fin_two.mpr ⟨?_, ?_⟩⟩
  · exact fourierTable_zero_zero d
  · exact fourierTable_zero_one d
  · exact fourierTable_one_zero d
  · exact fourierTable_one_one d

end

end CGLMPBounds
