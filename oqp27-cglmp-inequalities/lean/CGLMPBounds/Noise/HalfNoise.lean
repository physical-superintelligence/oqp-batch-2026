module

public import CGLMPBounds.Defs.Visibility
public import CGLMPBounds.Scenario.HiddenVariable
public import CGLMPBounds.CGLMP.LocalBound

@[expose] public section


/-!
# Uniform-noise local models and lower bounds on the critical visibility

Manuscript locators: Appendix F.1, equation (F.4) and the derivation of (F.3) in the proof of
Lemma F.1; Appendix B (critical visibility).

* `half_noise_mem_localSet` : (F.4) for a nonnegative table `q_rem` with uniform one-party
  marginals (hence no-signalling), `(q_rem + u) / 2` is Bell-local.
* `noisy_mem_localSet_of_local_part` : if `q = t L + (1 - t) q_rem` with `L` local and
  `(q_rem + u) / 2` local, then the noise mixture of `q` at visibility `1 / (2 - t)` is local.
* `le_critVisibility`, `le_critVisibility_of_local_part` : the resulting lower bound
  `v_crit(q) ≥ 1 / (2 - t)`, the abstract form of (F.3).
* `critVisibility_le_two_div_cglmp` : `v_crit(q) ≤ 2 / I_d(q)` when `I_d(q) > 2`.
-/

namespace CGLMPBounds

noncomputable section

theorem sum_fin_two_ite (P K : ℝ) :
    ∀ x : Fin 2, ∑ g : Fin 2, (if x = g then P else K) = P + K := by
  refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
  · rw [Fin.sum_univ_two, if_pos rfl, if_neg (show ¬((0 : Fin 2) = 1) by decide)]
  · rw [Fin.sum_univ_two, if_neg (show ¬((1 : Fin 2) = 0) by decide), if_pos rfl, add_comm]

theorem half_mul_inv_mul_cancel (n A Q : ℝ) (hn : n ≠ 0) :
    1 / 2 * (1 / n) * (A * (n * Q)) = 1 / 2 * (A * Q) := by
  have h : 1 / n * n = 1 := by rw [one_div, inv_mul_cancel₀ hn]
  linear_combination (1 / 2 * A * Q) * h

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- **Equation (F.4).** If `q` is nonnegative with uniform one-party marginals, then the
half-noise mixture `(q + u) / 2` is Bell-local. The local model guesses Alice's input uniformly,
samples her output for the guessed input uniformly, samples Bob's two outputs conditionally
according to `q`, and makes Alice's other output independent and uniform. -/
theorem half_noise_mem_localSet [Nonempty α] {q : Table α β} (hq0 : ∀ x y a b, 0 ≤ q x y a b)
    (hA : ∀ x y a, ∑ b, q x y a b = 1 / (Fintype.card α : ℝ))
    (hB : ∀ x y b, ∑ a, q x y a b = 1 / (Fintype.card β : ℝ)) :
    (1 / 2 : ℝ) • q + (1 / 2 : ℝ) • uniformTable α β ∈ localSet α β := by
  have hn : (Fintype.card α : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hinv : 1 / (Fintype.card α : ℝ) * (Fintype.card α : ℝ) = 1 := by
    rw [one_div, inv_mul_cancel₀ hn]
  have hpos : (0 : ℝ) ≤ 1 / (Fintype.card α : ℝ) :=
    div_nonneg zero_le_one (Nat.cast_nonneg _)
  have hp1 : ∑ _l : Fin 2 × α, (1 / 2 * (1 / (Fintype.card α : ℝ))) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    linear_combination hinv
  have hA0 : ∀ (l : Fin 2 × α) (x : Fin 2) (a : α),
      (0 : ℝ) ≤ if x = l.1 then (if a = l.2 then 1 else 0) else 1 / (Fintype.card α : ℝ) := by
    intro l x a
    split_ifs
    · exact zero_le_one
    · exact le_rfl
    · exact hpos
  have hA1 : ∀ (l : Fin 2 × α) (x : Fin 2),
      ∑ a : α, (if x = l.1 then (if a = l.2 then (1 : ℝ) else 0)
        else 1 / (Fintype.card α : ℝ)) = 1 := by
    intro l x
    by_cases h : x = l.1
    · simp only [if_pos h]
      rw [Finset.sum_eq_single_of_mem l.2 (Finset.mem_univ _)]
      · rw [if_pos rfl]
      · intro c _ hc
        rw [if_neg hc]
    · simp only [if_neg h]
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      linear_combination hinv
  have hB0 : ∀ (l : Fin 2 × α) (y : Fin 2) (b : β),
      (0 : ℝ) ≤ (Fintype.card α : ℝ) * q l.1 y l.2 b :=
    fun l y b => mul_nonneg (Nat.cast_nonneg _) (hq0 _ _ _ _)
  have hB1 : ∀ (l : Fin 2 × α) (y : Fin 2),
      ∑ b : β, (Fintype.card α : ℝ) * q l.1 y l.2 b = 1 := by
    intro l y
    rw [← Finset.mul_sum, hA]
    linear_combination hinv
  have hmodel := lhv_mem_localSet (α := α) (β := β)
    (fun _ : Fin 2 × α => 1 / 2 * (1 / (Fintype.card α : ℝ)))
    (fun _ => mul_nonneg (by norm_num) hpos) hp1
    (fun l x a => if x = l.1 then (if a = l.2 then 1 else 0) else 1 / (Fintype.card α : ℝ))
    (fun l y b => (Fintype.card α : ℝ) * q l.1 y l.2 b) hA0 hA1 hB0 hB1
  have hEq : ((1 / 2 : ℝ) • q + (1 / 2 : ℝ) • uniformTable α β)
      = (fun x y a b => ∑ l : Fin 2 × α, 1 / 2 * (1 / (Fintype.card α : ℝ))
          * ((if x = l.1 then (if a = l.2 then 1 else 0) else 1 / (Fintype.card α : ℝ))
            * ((Fintype.card α : ℝ) * q l.1 y l.2 b))) := by
    funext x y a b
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, uniformTable, Fintype.sum_prod_type,
      half_mul_inv_mul_cancel _ _ _ hn]
    have inner : ∀ g : Fin 2,
        ∑ c : α, 1 / 2 * ((if x = g then (if a = c then (1 : ℝ) else 0)
            else 1 / (Fintype.card α : ℝ)) * q g y c b)
          = if x = g then 1 / 2 * q x y a b
            else 1 / 2 * (1 / ((Fintype.card α : ℝ) * (Fintype.card β : ℝ))) := by
      intro g
      by_cases h : x = g
      · simp only [if_pos h]
        rw [Finset.sum_eq_single_of_mem a (Finset.mem_univ a)]
        · rw [if_pos rfl, one_mul, h]
        · intro c _ hc
          rw [if_neg (fun e => hc e.symm), zero_mul, mul_zero]
      · simp only [if_neg h, ← Finset.mul_sum, hB]
        ring
    simp only [inner]
    rw [sum_fin_two_ite]
  rw [hEq]
  exact hmodel

/-- If `q = t L + (1 - t) r` with `L` Bell-local and `(r + u) / 2` Bell-local, then the
uniform-noise mixture of `q` at visibility `1 / (2 - t)` is Bell-local. -/
theorem noisy_mem_localSet_of_local_part {q L r : Table α β} {t : ℝ} (ht1 : t ≤ 1)
    (ht0 : 0 ≤ t) (hL : L ∈ localSet α β)
    (hr : (1 / 2 : ℝ) • r + (1 / 2 : ℝ) • uniformTable α β ∈ localSet α β)
    (hq : q = t • L + (1 - t) • r) :
    noisy (1 / (2 - t)) q ∈ localSet α β := by
  have h2 : (2 : ℝ) - t ≠ 0 := by
    intro h
    linarith
  have h2' : (0 : ℝ) ≤ 2 - t := by linarith
  have hw : (2 - t) * (1 / (2 - t)) = 1 := by rw [mul_one_div, div_self h2]
  have hEq : noisy (1 / (2 - t)) q
      = (t / (2 - t)) • L
        + (2 * (1 - t) / (2 - t)) • ((1 / 2 : ℝ) • r + (1 / 2 : ℝ) • uniformTable α β) := by
    subst hq
    funext x y a b
    simp only [noisy, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (-(uniformTable α β x y a b)) * hw
  rw [hEq]
  refine convex_convexHull ℝ _ hL hr (div_nonneg ht0 h2') (div_nonneg (by linarith) h2') ?_
  rw [← add_div, div_eq_one_iff_eq h2]
  ring

/-- A visibility at which the noise mixture is Bell-local is a lower bound for `v_crit`. -/
theorem le_critVisibility {q : Table α β} {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (h : noisy v q ∈ localSet α β) : v ≤ critVisibility q :=
  le_csSup ⟨1, fun _ hw => hw.2.1⟩ ⟨hv0, hv1, h⟩

/-- Abstract form of (F.3): a local part of weight `t` with a half-noise-local remainder gives
`v_crit(q) ≥ 1 / (2 - t)`. -/
theorem le_critVisibility_of_local_part {q L r : Table α β} {t : ℝ} (ht1 : t ≤ 1)
    (ht0 : 0 ≤ t) (hL : L ∈ localSet α β)
    (hr : (1 / 2 : ℝ) • r + (1 / 2 : ℝ) • uniformTable α β ∈ localSet α β)
    (hq : q = t • L + (1 - t) • r) :
    1 / (2 - t) ≤ critVisibility q := by
  have h2 : (0 : ℝ) < 2 - t := by linarith
  refine le_critVisibility (div_nonneg zero_le_one h2.le) ?_
    (noisy_mem_localSet_of_local_part ht1 ht0 hL hr hq)
  rw [div_le_one h2]
  linarith

/-- The global critical visibility is at most the CGLMP witness threshold `2 / I_d(q)`. -/
theorem critVisibility_le_two_div_cglmp (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    {q : Table (ZMod d) (ZMod d)} (hq : 2 < cglmp d q) :
    critVisibility q ≤ 2 / cglmp d q :=
  Real.sSup_le (fun _ hv => visibility_le_of_noisy_mem_localSet d hd hq hv.2.2)
    (div_nonneg zero_le_two (by linarith))

end

end CGLMPBounds
