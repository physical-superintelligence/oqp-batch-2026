module

public import CGLMPBounds.Statistics.Ceiling
public import CGLMPBounds.TensorCHSH.Truncation

@[expose] public section


/-!
# Data processing for the relative entropy and the statistical strength

Supplement, text before (F.7): "Discarding all but the first `M` output bits maps `T_m` to `T_M` [...]
Data processing and preservation of the noise mixture therefore give `v_crit(T_m) ≤ v_crit(T_M)`
and `S_μ(T_m) ≥ S_μ(T_M)`" (F.7); proof of Theorem A.4: "Data processing, retaining the context and
both the event and its complement, gives [...]".

* `log_sum_le` : the log-sum inequality;
* `pushforward`, `relEntropy_pushforward_le` : `D(f_* p ‖ f_* r) ≤ D(p ‖ r)` for nonnegative vectors;
* `statStrength_coarseGrain_le` : `S_μ(coarseGrain f g q) ≤ S_μ(q)`;
* `statStrength_tensorTable_le` : statistical half of (F.7), `S_μ(T_M) ≤ S_μ(T_m)` for `M ≤ m`.
-/

namespace CGLMPBounds

noncomputable section

open scoped ENNReal

/-- The log-sum inequality `(Σ a) log(Σ a / Σ b) ≤ Σ_i a_i log(a_i / b_i)` for nonnegative `a, b`
with `b_i = 0 → a_i = 0`. -/
theorem log_sum_le {ι : Type*} (s : Finset ι) (a b : ι → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i)
    (hb : ∀ i ∈ s, 0 ≤ b i) (hab : ∀ i ∈ s, b i = 0 → a i = 0) :
    (∑ i ∈ s, a i) * Real.log ((∑ i ∈ s, a i) / ∑ i ∈ s, b i)
      ≤ ∑ i ∈ s, a i * Real.log (a i / b i) := by
  have hA0 : 0 ≤ ∑ i ∈ s, a i := Finset.sum_nonneg ha
  rcases eq_or_lt_of_le hA0 with h | h
  · have hz : ∀ i ∈ s, a i = 0 := (Finset.sum_eq_zero_iff_of_nonneg ha).mp h.symm
    rw [← h, zero_mul]
    exact (Finset.sum_eq_zero (fun i hi => by rw [hz i hi, zero_mul])).ge
  obtain ⟨i₀, hi₀, hai₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero h.ne'
  have hB : 0 < ∑ i ∈ s, b i := by
    have hbi : 0 < b i₀ := lt_of_le_of_ne (hb i₀ hi₀) (fun h' => hai₀ (hab i₀ hi₀ h'.symm))
    exact lt_of_lt_of_le hbi (Finset.single_le_sum hb hi₀)
  have hc : 0 < (∑ i ∈ s, a i) / ∑ i ∈ s, b i := div_pos h hB
  have key : ∀ j ∈ s, a j * Real.log ((∑ i ∈ s, a i) / ∑ i ∈ s, b i) + a j
      - b j * ((∑ i ∈ s, a i) / ∑ i ∈ s, b i) ≤ a j * Real.log (a j / b j) := by
    intro j hj
    rcases eq_or_lt_of_le (ha j hj) with h0 | h0
    · rw [← h0, zero_mul, zero_add, zero_sub, zero_mul]
      exact neg_nonpos.mpr (mul_nonneg (hb j hj) hc.le)
    have hbj : 0 < b j := lt_of_le_of_ne (hb j hj) (fun h' => h0.ne' (hab j hj h'.symm))
    have hx : 0 < a j / b j / ((∑ i ∈ s, a i) / ∑ i ∈ s, b i) := div_pos (div_pos h0 hbj) hc
    have h1 := Real.one_sub_inv_le_log_of_pos hx
    rw [Real.log_div (div_pos h0 hbj).ne' hc.ne', inv_div] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 h0.le
    have e : a j * (1 - (∑ i ∈ s, a i) / (∑ i ∈ s, b i) / (a j / b j))
        = a j - b j * ((∑ i ∈ s, a i) / ∑ i ∈ s, b i) := by
      rw [div_div_eq_mul_div, mul_sub, mul_one, mul_div_assoc', mul_div_cancel_left₀ _ h0.ne']
      ring
    rw [e, mul_sub] at h2
    linarith
  have hsum := Finset.sum_le_sum key
  have e1 : ∑ j ∈ s, (a j * Real.log ((∑ i ∈ s, a i) / ∑ i ∈ s, b i) + a j
      - b j * ((∑ i ∈ s, a i) / ∑ i ∈ s, b i))
      = (∑ i ∈ s, a i) * Real.log ((∑ i ∈ s, a i) / ∑ i ∈ s, b i) + ∑ i ∈ s, a i
        - (∑ i ∈ s, b i) * ((∑ i ∈ s, a i) / ∑ i ∈ s, b i) := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
  have e2 : (∑ i ∈ s, b i) * ((∑ i ∈ s, a i) / ∑ i ∈ s, b i) = ∑ i ∈ s, a i := by
    rw [mul_div_assoc', mul_div_cancel_left₀ _ hB.ne']
  rw [e1, e2] at hsum
  linarith

/-- Pushforward `(f_* p)(k) = Σ_{f i = k} p_i` of a finite vector along a map. -/
def pushforward {ι κ : Type*} [Fintype ι] [DecidableEq κ] (f : ι → κ) (p : ι → ℝ) (k : κ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => f i = k), p i

/-- Data processing: `D(f_* p ‖ f_* r) ≤ D(p ‖ r)` for nonnegative vectors. -/
theorem relEntropy_pushforward_le {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (f : ι → κ) {p r : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (hr : ∀ i, 0 ≤ r i) :
    relEntropy (pushforward f p) (pushforward f r) ≤ relEntropy p r := by
  by_cases hac : ∀ i, r i = 0 → p i = 0
  · have hac' : ∀ k, pushforward f r k = 0 → pushforward f p k = 0 := by
      intro k hk
      have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hr i)).mp hk
      exact Finset.sum_eq_zero (fun i hi => hac i (hz i hi))
    unfold relEntropy
    rw [if_pos hac', if_pos hac]
    apply ENNReal.ofReal_le_ofReal
    rw [← Finset.sum_fiberwise Finset.univ f (fun i => p i * Real.logb 2 (p i / r i))]
    refine Finset.sum_le_sum (fun k _ => ?_)
    have hls := log_sum_le (Finset.univ.filter (fun i => f i = k)) p r (fun i _ => hp i)
      (fun i _ => hr i) (fun i _ => hac i)
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have e1 : pushforward f p k * Real.logb 2 (pushforward f p k / pushforward f r k)
        = (∑ i ∈ Finset.univ.filter (fun i => f i = k), p i)
          * Real.log ((∑ i ∈ Finset.univ.filter (fun i => f i = k), p i)
            / ∑ i ∈ Finset.univ.filter (fun i => f i = k), r i) / Real.log 2 := by
      unfold pushforward Real.logb
      ring
    have e2 : ∑ i ∈ Finset.univ.filter (fun i => f i = k), p i * Real.logb 2 (p i / r i)
        = (∑ i ∈ Finset.univ.filter (fun i => f i = k), p i * Real.log (p i / r i))
          / Real.log 2 := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      unfold Real.logb
      ring
    rw [e1, e2]
    exact div_le_div_of_nonneg_right hls hlog2.le
  · unfold relEntropy
    rw [if_neg hac]
    exact le_top

/-- The outcome distribution of a coarse-grained table in a context is a pushforward. -/
theorem coarseGrain_eq_pushforward {α β α' β' : Type*} [Fintype α] [Fintype β] [DecidableEq α']
    [DecidableEq β'] (f : α → α') (g : β → β') (T : Table α β) (x y : Fin 2) :
    (fun z : α' × β' => coarseGrain f g T x y z.1 z.2)
      = pushforward (fun z : α × β => (f z.1, g z.2)) (fun z => T x y z.1 z.2) := by
  funext z
  show coarseGrain f g T x y z.1 z.2 = pushforward (fun z : α × β => (f z.1, g z.2))
    (fun z => T x y z.1 z.2) z
  rw [TensorCHSH.coarseGrain_apply]
  unfold pushforward
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  by_cases h : z.1 = f a ∧ z.2 = g b
  · have h' : (f a, g b) = z := Prod.ext h.1.symm h.2.symm
    rw [if_pos h]
    exact (if_pos h').symm
  · have h' : ¬(f a, g b) = z := fun e => h ⟨by rw [← e], by rw [← e]⟩
    rw [if_neg h]
    exact (if_neg h').symm

/-- Data processing for the statistical strength: coarse-graining outcomes cannot increase
`S_μ`. -/
theorem statStrength_coarseGrain_le {α β α' β' : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    [DecidableEq β] [Fintype α'] [Fintype β'] [DecidableEq α'] [DecidableEq β'] (f : α → α')
    (g : β → β') (μ : Fin 2 → Fin 2 → ℝ) {q : Table α β} (hq : ∀ x y a b, 0 ≤ q x y a b) :
    statStrength μ (coarseGrain f g q) ≤ statStrength μ q := by
  unfold statStrength
  refine le_iInf₂ (fun ℓ hℓ => ?_)
  have hℓ0 := (isNoSignalling_of_mem_localSet hℓ).isBehaviour.nonneg
  refine (iInf₂_le (coarseGrain f g ℓ) (coarseGrain_mem_localSet f g hℓ)).trans ?_
  refine Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun y _ => ?_))
  refine mul_le_mul_of_nonneg_left ?_ zero_le
  rw [coarseGrain_eq_pushforward f g q x y, coarseGrain_eq_pushforward f g ℓ x y]
  exact relEntropy_pushforward_le _ (fun z => hq x y z.1 z.2) (fun z => hℓ0 x y z.1 z.2)

theorem tensorTable_nonneg {m : ℕ} {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (x y : Fin 2)
    (a b : Fin m → Bool) : 0 ≤ TensorCHSH.tensorTable m ρ x y a b :=
  mul_nonneg (pow_nonneg (by norm_num) _)
    (mul_nonneg (pow_nonneg (sub_nonneg.mpr hρ1) _) (pow_nonneg hρ0 _))

/-- Dropping the last output bit cannot increase `S_μ`: `S_μ(T_M) ≤ S_μ(T_{M+1})`. -/
theorem statStrength_tensorTable_succ_le (μ : Fin 2 → Fin 2 → ℝ) (M : ℕ) {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ ≤ 1) :
    statStrength μ (TensorCHSH.tensorTable M ρ)
      ≤ statStrength μ (TensorCHSH.tensorTable (M + 1) ρ) := by
  have hc := statStrength_coarseGrain_le (Fin.init (α := fun _ : Fin (M + 1) => Bool))
    (Fin.init (α := fun _ : Fin (M + 1) => Bool)) μ (tensorTable_nonneg (m := M + 1) hρ0 hρ1)
  rwa [TensorCHSH.coarseGrain_init_tensorTable] at hc

/-- Statistical half of (F.7): `S_μ(T_M) ≤ S_μ(T_m)` for `M ≤ m` (discard output bits). -/
theorem statStrength_tensorTable_le (μ : Fin 2 → Fin 2 → ℝ) {M m : ℕ} (h : M ≤ m) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    statStrength μ (TensorCHSH.tensorTable M ρ) ≤ statStrength μ (TensorCHSH.tensorTable m ρ) := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (statStrength_tensorTable_succ_le μ _ hρ0 hρ1)

end

end CGLMPBounds
