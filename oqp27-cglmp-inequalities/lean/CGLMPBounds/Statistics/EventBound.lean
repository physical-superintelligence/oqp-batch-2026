module

public import CGLMPBounds.Statistics.DataProcessing
public import CGLMPBounds.TensorCHSH.Witness

@[expose] public section


/-!
# Event lower bounds for the statistical strength of the tensor CHSH behaviour

Supplement, proof of Theorem A.4 and (F.16): "Use `T_m` from (F.5) and the strict events
`A_xy = {K_xy < m/4}` [...] By (F.6), at most three of the four events hold on a deterministic local
assignment. Thus local event probabilities obey `Σ_e z_e ≤ 3`. Data processing, retaining the
context and both the event and its complement, gives `S_μ(T_m) ≥ min Σ_e μ_e D_bin(t_m‖z_e)`."
"For uniform inputs and `t > 3/4`, convexity gives `min (1/4) Σ_e D_bin(t‖z_e) = D_bin(t‖3/4)`."

Here the events are `K_xy ≤ k` with `4k < m` (for `m = 41`, `k = 10`).

* `binRelEntropy` : `D_bin(t‖z)` in bits;
* `TensorCHSH.sum_eventProb_le_three` : `Σ_e ℓ_e(A_e) ≤ 3` on the local set;
* `TensorCHSH.binRelEntropy_eventProb_le` : binary data processing in one context;
* `binRelEntropy_le_avg` : the uniform-input minimisation, by the tangent line at `3/4`;
* `TensorCHSH.binRelEntropy_le_statStrength` : `D_bin(t‖3/4) ≤ S_unif(q)` when every context has
  event probability `t ∈ (3/4, 1)`.
-/

namespace CGLMPBounds

noncomputable section

open scoped ENNReal

/-- Binary relative entropy `D_bin(t‖z)` in bits. -/
def binRelEntropy (t z : ℝ) : ℝ≥0∞ :=
  relEntropy (fun c : Bool => if c then t else 1 - t) (fun c : Bool => if c then z else 1 - z)

theorem binRelEntropy_of_mem {t z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    binRelEntropy t z = ENNReal.ofReal
      (t * Real.logb 2 (t / z) + (1 - t) * Real.logb 2 ((1 - t) / (1 - z))) := by
  unfold binRelEntropy relEntropy
  have hac : ∀ c : Bool, (if c then z else 1 - z) = 0 → (if c then t else 1 - t) = 0 := by
    intro c hc
    cases c
    · exact absurd (show (1 : ℝ) - z = 0 from hc) (sub_pos.mpr hz1).ne'
    · exact absurd (show z = 0 from hc) hz0.ne'
  rw [if_pos hac, Fintype.sum_bool]
  rfl

theorem binRelEntropy_zero {t : ℝ} (ht : 0 < t) : binRelEntropy t 0 = ∞ := by
  unfold binRelEntropy relEntropy
  rw [if_neg]
  intro h
  exact ht.ne' (h true rfl)

theorem binRelEntropy_one {t : ℝ} (ht : t < 1) : binRelEntropy t 1 = ∞ := by
  unfold binRelEntropy relEntropy
  rw [if_neg]
  intro h
  have h' := h false (show (1 : ℝ) - 1 = 0 by norm_num)
  exact (sub_pos.mpr ht).ne' h'

/-- Tangent line of `z ↦ D_bin(t‖z)` (in nats) at `3/4`. -/
theorem binKL_tangent {t z : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hz0 : 0 < z) (hz1 : z < 1) :
    t * Real.log (t / (3 / 4)) + (1 - t) * Real.log ((1 - t) / (1 - 3 / 4))
        + (4 - 16 / 3 * t) * (z - 3 / 4)
      ≤ t * Real.log (t / z) + (1 - t) * Real.log ((1 - t) / (1 - z)) := by
  have h1 := Real.log_le_sub_one_of_pos (div_pos hz0 (by norm_num : (0 : ℝ) < 3 / 4))
  have h2 := Real.log_le_sub_one_of_pos (div_pos (sub_pos.mpr hz1) (by norm_num : (0 : ℝ) < 1 / 4))
  rw [Real.log_div hz0.ne' (by norm_num : (3 / 4 : ℝ) ≠ 0)] at h1
  rw [Real.log_div (sub_pos.mpr hz1).ne' (by norm_num : (1 / 4 : ℝ) ≠ 0)] at h2
  have e1 : z / (3 / 4) = 4 / 3 * z := by ring
  have e2 : (1 - z) / (1 / 4) = 4 - 4 * z := by ring
  rw [e1] at h1
  rw [e2] at h2
  have e3 : (1 : ℝ) - 3 / 4 = 1 / 4 := by norm_num
  rw [e3, Real.log_div ht0.ne' (by norm_num : (3 / 4 : ℝ) ≠ 0), Real.log_div ht0.ne' hz0.ne',
    Real.log_div (sub_pos.mpr ht1).ne' (by norm_num : (1 / 4 : ℝ) ≠ 0),
    Real.log_div (sub_pos.mpr ht1).ne' (sub_pos.mpr hz1).ne']
  nlinarith [mul_le_mul_of_nonneg_left h1 ht0.le, mul_le_mul_of_nonneg_left h2 (sub_pos.mpr ht1).le]

/-- The uniform-input minimisation: if `0 ≤ z_e ≤ 1`, `Σ_e z_e ≤ 3` and `3/4 < t < 1`, then
`D_bin(t‖3/4) ≤ (1/4) Σ_e D_bin(t‖z_e)`. -/
theorem binRelEntropy_le_avg {t : ℝ} (ht : 3 / 4 < t) (ht1 : t < 1) {z : Fin 2 → Fin 2 → ℝ}
    (hz : ∀ x y, 0 ≤ z x y ∧ z x y ≤ 1) (h3 : ∑ x, ∑ y, z x y ≤ 3) :
    binRelEntropy t (3 / 4) ≤ ∑ x, ∑ y, ENNReal.ofReal (1 / 4) * binRelEntropy t (z x y) := by
  have ht0 : 0 < t := by linarith
  have hq : ENNReal.ofReal (1 / 4) ≠ 0 := (ENNReal.ofReal_pos.mpr (by norm_num)).ne'
  have htop : ∀ x y, (z x y = 0 ∨ z x y = 1) →
      ∑ x, ∑ y, ENNReal.ofReal (1 / 4) * binRelEntropy t (z x y) = ∞ := by
    intro x y hxy
    have hterm : ENNReal.ofReal (1 / 4) * binRelEntropy t (z x y) = ∞ := by
      rcases hxy with h | h
      · rw [h, binRelEntropy_zero ht0, ENNReal.mul_top hq]
      · rw [h, binRelEntropy_one ht1, ENNReal.mul_top hq]
    have hle : ENNReal.ofReal (1 / 4) * binRelEntropy t (z x y)
        ≤ ∑ x', ∑ y', ENNReal.ofReal (1 / 4) * binRelEntropy t (z x' y') :=
      (Finset.single_le_sum (f := fun y' => ENNReal.ofReal (1 / 4) * binRelEntropy t (z x y'))
        (fun _ _ => zero_le) (Finset.mem_univ y)).trans
      (Finset.single_le_sum (f := fun x' => ∑ y', ENNReal.ofReal (1 / 4) * binRelEntropy t (z x' y'))
        (fun _ _ => zero_le) (Finset.mem_univ x))
    rw [hterm] at hle
    exact top_le_iff.mp hle
  by_cases hbad : ∃ x y, z x y = 0 ∨ z x y = 1
  · obtain ⟨x, y, hxy⟩ := hbad
    rw [htop x y hxy]
    exact le_top
  push_neg at hbad
  have hin : ∀ x y, 0 < z x y ∧ z x y < 1 := fun x y =>
    ⟨lt_of_le_of_ne (hz x y).1 (Ne.symm (hbad x y).1), lt_of_le_of_ne (hz x y).2 (hbad x y).2⟩
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hG : ∀ w : ℝ, t * Real.logb 2 (t / w) + (1 - t) * Real.logb 2 ((1 - t) / (1 - w))
      = (t * Real.log (t / w) + (1 - t) * Real.log ((1 - t) / (1 - w))) / Real.log 2 := by
    intro w
    unfold Real.logb
    ring
  have hnat : t * Real.log (t / (3 / 4)) + (1 - t) * Real.log ((1 - t) / (1 - 3 / 4))
      ≤ 1 / 4 * (t * Real.log (t / z 0 0) + (1 - t) * Real.log ((1 - t) / (1 - z 0 0)))
        + 1 / 4 * (t * Real.log (t / z 0 1) + (1 - t) * Real.log ((1 - t) / (1 - z 0 1)))
        + (1 / 4 * (t * Real.log (t / z 1 0) + (1 - t) * Real.log ((1 - t) / (1 - z 1 0)))
          + 1 / 4 * (t * Real.log (t / z 1 1) + (1 - t) * Real.log ((1 - t) / (1 - z 1 1)))) := by
    have k00 := binKL_tangent ht0 ht1 (hin 0 0).1 (hin 0 0).2
    have k01 := binKL_tangent ht0 ht1 (hin 0 1).1 (hin 0 1).2
    have k10 := binKL_tangent ht0 ht1 (hin 1 0).1 (hin 1 0).2
    have k11 := binKL_tangent ht0 ht1 (hin 1 1).1 (hin 1 1).2
    simp only [Fin.sum_univ_two] at h3
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ 16 / 3 * t - 4 by linarith)
      (show (0 : ℝ) ≤ 3 - (z 0 0 + z 0 1 + (z 1 0 + z 1 1)) by linarith)]
  have hreal : t * Real.logb 2 (t / (3 / 4)) + (1 - t) * Real.logb 2 ((1 - t) / (1 - 3 / 4))
      ≤ 1 / 4 * (t * Real.logb 2 (t / z 0 0) + (1 - t) * Real.logb 2 ((1 - t) / (1 - z 0 0)))
        + 1 / 4 * (t * Real.logb 2 (t / z 0 1) + (1 - t) * Real.logb 2 ((1 - t) / (1 - z 0 1)))
        + (1 / 4 * (t * Real.logb 2 (t / z 1 0) + (1 - t) * Real.logb 2 ((1 - t) / (1 - z 1 0)))
          + 1 / 4 * (t * Real.logb 2 (t / z 1 1)
            + (1 - t) * Real.logb 2 ((1 - t) / (1 - z 1 1)))) := by
    simp only [hG]
    refine (div_le_div_of_nonneg_right hnat hlog2.le).trans (le_of_eq ?_)
    ring
  rw [binRelEntropy_of_mem (t := t) (z := 3 / 4) (by norm_num) (by norm_num)]
  simp only [fun x y => binRelEntropy_of_mem (t := t) (hin x y).1 (hin x y).2, Fin.sum_univ_two]
  rw [← ENNReal.ofReal_mul (p := 1 / 4) (by norm_num), ← ENNReal.ofReal_mul (p := 1 / 4) (by norm_num),
    ← ENNReal.ofReal_mul (p := 1 / 4) (by norm_num), ← ENNReal.ofReal_mul (p := 1 / 4) (by norm_num)]
  exact (ENNReal.ofReal_le_ofReal hreal).trans ((ENNReal.ofReal_add_le).trans
    (add_le_add ENNReal.ofReal_add_le ENNReal.ofReal_add_le))

namespace TensorCHSH

/-- Indicator table of the events `K_xy ≤ k`. -/
def eventTable (m k : ℕ) : Table (Fin m → Bool) (Fin m → Bool) :=
  fun x y a b => if errCount x y a b ≤ k then 1 else 0

/-- Probability of the event `K_xy ≤ k` in the context `(x, y)`. -/
def eventProb {m : ℕ} (k : ℕ) (q : Table (Fin m → Bool) (Fin m → Bool)) (x y : Fin 2) : ℝ :=
  ∑ a, ∑ b, eventTable m k x y a b * q x y a b

/-- The event indicator `(a, b) ↦ decide (K_xy(a, b) ≤ k)`. -/
def eventMap (m k : ℕ) (x y : Fin 2) (z : (Fin m → Bool) × (Fin m → Bool)) : Bool :=
  decide (errCount x y z.1 z.2 ≤ k)

/-- (F.6) for events: on the Bell-local set, at most three of the four events `K_xy ≤ k` hold in
expectation, `Σ_xy ℓ_xy(K_xy ≤ k) ≤ 3`, whenever `4k < m`. -/
theorem sum_eventProb_le_three {m k : ℕ} (hk : 4 * k < m)
    {ℓ : Table (Fin m → Bool) (Fin m → Bool)} (hℓ : ℓ ∈ localSet _ _) :
    ∑ x, ∑ y, eventProb k ℓ x y ≤ 3 := by
  have h : bell (eventTable m k) ℓ ≤ 3 := by
    refine bell_le_of_mem_localSet (fun s => ?_) hℓ
    rw [bell_detTable]
    have hcount := le_sum_errCount s.1 s.2
    simp only [eventTable, Fin.sum_univ_two] at hcount ⊢
    split_ifs <;> norm_num <;> omega
  rw [bell_apply] at h
  exact h

/-- In each context the binary vector `(t, 1 - t)` of the event is the pushforward of the outcome
distribution. -/
theorem pushforward_eventMap {m : ℕ} (k : ℕ) (T : Table (Fin m → Bool) (Fin m → Bool))
    (hT : ∀ x y, ∑ a, ∑ b, T x y a b = 1) (x y : Fin 2) :
    pushforward (eventMap m k x y) (fun z => T x y z.1 z.2)
      = fun c : Bool => if c then eventProb k T x y else 1 - eventProb k T x y := by
  have htrue : pushforward (eventMap m k x y) (fun z => T x y z.1 z.2) true = eventProb k T x y := by
    unfold pushforward eventProb eventTable
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    by_cases h : errCount x y a b ≤ k <;> simp [eventMap, h]
  have htot : pushforward (eventMap m k x y) (fun z => T x y z.1 z.2) true
      + pushforward (eventMap m k x y) (fun z => T x y z.1 z.2) false = 1 := by
    have h1 := Finset.sum_fiberwise Finset.univ (eventMap m k x y) (fun z => T x y z.1 z.2)
    rw [Fintype.sum_bool, Fintype.sum_prod_type', hT] at h1
    exact h1
  funext c
  cases c
  · rw [if_neg (by decide)]
    linarith
  · rw [if_pos rfl]
    exact htrue

/-- Binary data processing in one context: `D_bin(q(A)‖ℓ(A)) ≤ D(q_xy‖ℓ_xy)`. -/
theorem binRelEntropy_eventProb_le {m : ℕ} (k : ℕ) {q ℓ : Table (Fin m → Bool) (Fin m → Bool)}
    (hq : IsBehaviour q) (hℓ : IsBehaviour ℓ) (x y : Fin 2) :
    binRelEntropy (eventProb k q x y) (eventProb k ℓ x y)
      ≤ relEntropy (fun z : (Fin m → Bool) × (Fin m → Bool) => q x y z.1 z.2)
          (fun z => ℓ x y z.1 z.2) := by
  unfold binRelEntropy
  rw [← pushforward_eventMap k q hq.sum_eq_one x y, ← pushforward_eventMap k ℓ hℓ.sum_eq_one x y]
  exact relEntropy_pushforward_le _ (fun z => hq.nonneg x y z.1 z.2) (fun z => hℓ.nonneg x y z.1 z.2)

/-- Event lower bound for uniform inputs: if every context of the behaviour `q` gives the event
`K_xy ≤ k` (with `4k < m`) the same probability `t ∈ (3/4, 1)`, then `D_bin(t‖3/4) ≤ S_unif(q)`. -/
theorem binRelEntropy_le_statStrength {m k : ℕ} (hk : 4 * k < m)
    {q : Table (Fin m → Bool) (Fin m → Bool)} (hq : IsBehaviour q) {t : ℝ} (ht : 3 / 4 < t)
    (ht1 : t < 1) (hqt : ∀ x y, eventProb k q x y = t) :
    binRelEntropy t (3 / 4) ≤ statStrength (fun _ _ => 1 / 4) q := by
  unfold statStrength
  refine le_iInf₂ (fun ℓ hℓ => ?_)
  have hℓb := (isNoSignalling_of_mem_localSet hℓ).isBehaviour
  have hz : ∀ x y, 0 ≤ eventProb k ℓ x y ∧ eventProb k ℓ x y ≤ 1 := by
    intro x y
    have h0 : ∀ a b, 0 ≤ eventTable m k x y a b * ℓ x y a b := fun a b =>
      mul_nonneg (by unfold eventTable; split_ifs <;> norm_num) (hℓb.nonneg x y a b)
    have h1 : ∀ a b, eventTable m k x y a b * ℓ x y a b ≤ ℓ x y a b := fun a b => by
      unfold eventTable
      split_ifs
      · exact (one_mul _).le
      · rw [zero_mul]
        exact hℓb.nonneg x y a b
    refine ⟨Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => h0 a b)), ?_⟩
    calc eventProb k ℓ x y ≤ ∑ a, ∑ b, ℓ x y a b :=
          Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => h1 a b))
      _ = 1 := hℓb.sum_eq_one x y
  refine (binRelEntropy_le_avg ht ht1 hz (sum_eventProb_le_three hk hℓ)).trans ?_
  refine Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun y _ => ?_))
  refine mul_le_mul_of_nonneg_left ?_ zero_le
  rw [← hqt x y]
  exact binRelEntropy_eventProb_le k hq hℓb x y

end TensorCHSH

end

end CGLMPBounds
