module

public import CGLMPBounds.Statistics.Divergence
public import CGLMPBounds.Statistics.Gluing
public import CGLMPBounds.Statistics.Xi

@[expose] public section


/-!
# The universal statistical ceiling (Theorem F.2, equation (F.8))

Supplement, Theorem F.2: "For every no-signalling behaviour and every fixed input law,
`S_μ(q) ≤ [1 - LF(q)] Ξ(μ) ≤ Ξ(μ)`." Proof: for a feasible `s` of (B.6), the mixture `L*` of the
four gluings satisfies `L*_e ≥ s_e q_e`; apply this to the no-signalling remainder in
`q = t L + (1 - t) q_rem` and compare entrywise.

* `isNoSignalling_remainder` : `(q - t L)/(1 - t)` is no-signalling;
* `statStrength_le_of_local` : if `q ≥ t L` with `L` local and `0 ≤ t`, then
  `S_μ(q) ≤ (1 - t) Ξ(μ)`;
* `statStrength_le_localFraction` : `S_μ(q) ≤ [1 - LF(q)] Ξ(μ)`;
* `statistical_ceiling_spec` : (F.8).
-/

namespace CGLMPBounds

noncomputable section

open scoped ENNReal

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- Local tables have zero statistical strength. -/
theorem statStrength_eq_zero_of_mem_localSet (μ : Fin 2 → Fin 2 → ℝ) {q : Table α β}
    (hq : q ∈ localSet α β) : statStrength μ q = 0 := by
  refine le_antisymm ?_ (zero_le)
  unfold statStrength
  refine (iInf₂_le q hq).trans ?_
  simp only [relEntropy_self, mul_zero, Finset.sum_const_zero, le_refl]

/-- Two behaviours with `L ≤ q` entrywise are equal. -/
theorem table_eq_of_le {q L : Table α β} (hq : IsBehaviour q) (hL : IsBehaviour L)
    (h : ∀ x y a b, L x y a b ≤ q x y a b) : q = L := by
  funext x y a b
  have hsum : ∑ a', ∑ b', (q x y a' b' - L x y a' b') = 0 := by
    simp only [Finset.sum_sub_distrib]
    rw [hq.sum_eq_one, hL.sum_eq_one, sub_self]
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun a' _ => Finset.sum_nonneg
    (fun b' _ => sub_nonneg.mpr (h x y a' b')))).mp hsum a (Finset.mem_univ _)
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun b' _ => sub_nonneg.mpr (h x y a b'))).mp h1 b
    (Finset.mem_univ _)
  linarith

/-- For `t < 1`, the normalized remainder `(q - t L)/(1 - t)` of a no-signalling `q ≥ t L` with
`L` no-signalling is no-signalling. -/
theorem isNoSignalling_remainder {q L : Table α β} (hq : IsNoSignalling q)
    (hL : IsNoSignalling L) {t : ℝ} (ht1 : t < 1) (htL : ∀ x y a b, t * L x y a b ≤ q x y a b) :
    IsNoSignalling (fun x y a b => (q x y a b - t * L x y a b) / (1 - t)) := by
  have h1t : 0 < 1 - t := sub_pos.mpr ht1
  refine ⟨⟨fun x y a b => div_nonneg (sub_nonneg.mpr (htL x y a b)) h1t.le, fun x y => ?_⟩,
    fun x y y' a => ?_, fun x x' y b => ?_⟩
  · show ∑ a, ∑ b, (q x y a b - t * L x y a b) / (1 - t) = 1
    simp only [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [hq.isBehaviour.sum_eq_one, hL.isBehaviour.sum_eq_one, mul_one, div_self h1t.ne']
  · show ∑ b, (q x y a b - t * L x y a b) / (1 - t)
        = ∑ b, (q x y' a b - t * L x y' a b) / (1 - t)
    simp only [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [hq.margA_indep x y y' a, hL.margA_indep x y y' a]
  · show ∑ a, (q x y a b - t * L x y a b) / (1 - t)
        = ∑ a, (q x' y a b - t * L x' y a b) / (1 - t)
    simp only [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [hq.margB_indep x x' y b, hL.margB_indep x x' y b]

/-- If `q ≥ t L` entrywise with `L` Bell-local and `t ≥ 0`, then `S_μ(q) ≤ (1 - t) Ξ(μ)`. -/
theorem statStrength_le_of_local {q : Table α β} (hq : IsNoSignalling q)
    {μ : Fin 2 → Fin 2 → ℝ} (hμ : ∀ x y, 0 ≤ μ x y) {t : ℝ} (ht0 : 0 ≤ t) {L : Table α β}
    (hL : L ∈ localSet α β) (htL : ∀ x y a b, t * L x y a b ≤ q x y a b) :
    statStrength μ q ≤ ENNReal.ofReal (1 - t) * xiMin μ := by
  have hLns := isNoSignalling_of_mem_localSet hL
  rcases eq_or_lt_of_le (le_one_of_local_le hq hL htL) with ht | ht
  · have hqL : q = L := table_eq_of_le hq.isBehaviour hLns.isBehaviour
      (fun x y a b => by have h := htL x y a b; rw [ht, one_mul] at h; exact h)
    rw [hqL, statStrength_eq_zero_of_mem_localSet μ hL]
    exact zero_le
  have h1t : 0 < 1 - t := sub_pos.mpr ht
  have hc0 : ENNReal.ofReal (1 - t) ≠ 0 := (ENNReal.ofReal_pos.mpr h1t).ne'
  have hrns := isNoSignalling_remainder hq hLns ht htL
  unfold xiMin
  rw [ENNReal.mul_iInf_of_ne hc0 ENNReal.ofReal_ne_top]
  refine le_iInf (fun s => ?_)
  rw [ENNReal.mul_iInf_of_ne hc0 ENNReal.ofReal_ne_top]
  refine le_iInf (fun hs => ?_)
  obtain ⟨ℓr, hℓr, hge⟩ := exists_local_ge hrns hs.1 hs.2
  have hℓ : t • L + (1 - t) • ℓr ∈ localSet α β :=
    convex_convexHull ℝ _ hL hℓr ht0 h1t.le (by ring)
  unfold statStrength
  refine (iInf₂_le _ hℓ).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun x _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun y _ => ?_)
  by_cases hμ0 : μ x y = 0
  · rw [hμ0, ENNReal.ofReal_zero, zero_mul]
    exact zero_le
  by_cases hs0 : s x y = 0
  · have hne : ENNReal.ofReal (μ x y) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr (lt_of_le_of_ne (hμ x y) (Ne.symm hμ0))).ne'
    rw [hs0, negLogTwo_zero, ENNReal.mul_top hne, ENNReal.mul_top hc0]
    exact le_top
  have hspos : 0 < s x y := lt_of_le_of_ne (hs.1 x y).1 (Ne.symm hs0)
  have hcz : ∀ z : α × β, t * L x y z.1 z.2 + s x y * (q x y z.1 z.2 - t * L x y z.1 z.2)
      ≤ (t • L + (1 - t) • ℓr) x y z.1 z.2 := by
    intro z
    have hg : s x y * ((q x y z.1 z.2 - t * L x y z.1 z.2) / (1 - t)) ≤ ℓr x y z.1 z.2 :=
      hge x y z.1 z.2
    have e : s x y * (q x y z.1 z.2 - t * L x y z.1 z.2)
        = (1 - t) * (s x y * ((q x y z.1 z.2 - t * L x y z.1 z.2) / (1 - t))) := by
      rw [mul_div_assoc', mul_div_assoc', mul_div_cancel_left₀ _ h1t.ne']
    show _ ≤ t * L x y z.1 z.2 + (1 - t) * ℓr x y z.1 z.2
    rw [e]
    have h2 := mul_le_mul_of_nonneg_left hg h1t.le
    linarith
  have hsum : ∑ z : α × β, (q x y z.1 z.2 - t * L x y z.1 z.2) = 1 - t := by
    rw [Fintype.sum_prod_type' (fun a b => q x y a b - t * L x y a b)]
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [hq.isBehaviour.sum_eq_one, hLns.isBehaviour.sum_eq_one, mul_one]
  have hD := relEntropy_le_of_ge (p := fun z : α × β => q x y z.1 z.2)
    (c := fun z => t * L x y z.1 z.2) (a := fun z => q x y z.1 z.2 - t * L x y z.1 z.2)
    (fun z => by
      show q x y z.1 z.2 = t * L x y z.1 z.2 + (q x y z.1 z.2 - t * L x y z.1 z.2)
      ring)
    (fun z => mul_nonneg ht0 (hLns.isBehaviour.nonneg _ _ _ _))
    (fun z => sub_nonneg.mpr (htL _ _ _ _)) hspos (hs.1 x y).2 hcz
  rw [hsum] at hD
  refine (mul_le_mul_of_nonneg_left hD (zero_le)).trans (le_of_eq ?_)
  rw [negLogTwo_of_ne_zero hs0, ENNReal.ofReal_mul h1t.le]
  ring

theorem localFraction_set_nonempty {q : Table α β} (hq : IsNoSignalling q) :
    {t : ℝ | 0 ≤ t ∧ ∃ L ∈ localSet α β, ∀ x y a b, t * L x y a b ≤ q x y a b}.Nonempty := by
  obtain ⟨a0, -, ha0⟩ := Finset.exists_ne_zero_of_sum_ne_zero
    (show ∑ a, ∑ b, q 0 0 a b ≠ 0 by rw [hq.isBehaviour.sum_eq_one 0 0]; exact one_ne_zero)
  obtain ⟨b0, -, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero ha0
  refine ⟨0, le_refl 0, detTable (fun _ => a0, fun _ => b0),
    subset_convexHull ℝ _ ⟨(fun _ => a0, fun _ => b0), rfl⟩, fun x y a b => ?_⟩
  rw [zero_mul]
  exact hq.isBehaviour.nonneg x y a b

theorem localFraction_set_bddAbove {q : Table α β} (hq : IsNoSignalling q) :
    BddAbove {t : ℝ | 0 ≤ t ∧ ∃ L ∈ localSet α β, ∀ x y a b, t * L x y a b ≤ q x y a b} := by
  refine ⟨1, fun t ht => ?_⟩
  obtain ⟨_, L, hL, htL⟩ := ht
  exact le_one_of_local_le hq hL htL

theorem localFraction_nonneg {q : Table α β} (hq : IsNoSignalling q) : 0 ≤ localFraction q := by
  obtain ⟨t, ht⟩ := localFraction_set_nonempty hq
  exact ht.1.trans (le_csSup (localFraction_set_bddAbove hq) ht)

/-- Theorem F.2, first inequality of (F.8): `S_μ(q) ≤ [1 - LF(q)] Ξ(μ)`. -/
theorem statStrength_le_localFraction {q : Table α β} (hq : IsNoSignalling q)
    {μ : Fin 2 → Fin 2 → ℝ} (hμ : ∀ x y, 0 ≤ μ x y) (hμ1 : ∑ x, ∑ y, μ x y = 1) :
    statStrength μ q ≤ ENNReal.ofReal (1 - localFraction q) * xiMin μ := by
  have hfin : xiMin μ ≠ ∞ := xiMin_ne_top hμ hμ1
  have h1 : Continuous fun t : ℝ => ENNReal.ofReal (1 - t) :=
    ENNReal.continuous_ofReal.comp (continuous_const.sub continuous_id)
  have hcont : Continuous fun t : ℝ => ENNReal.ofReal (1 - t) * xiMin μ :=
    (ENNReal.continuous_mul_const hfin).comp h1
  have hanti : Antitone fun t : ℝ => ENNReal.ofReal (1 - t) * xiMin μ := fun t t' htt' =>
    mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (by linarith)) (zero_le)
  have key := hanti.map_csSup_of_continuousAt hcont.continuousAt
    (localFraction_set_nonempty hq) (localFraction_set_bddAbove hq)
  unfold localFraction
  rw [key]
  refine le_sInf ?_
  rintro _ ⟨t, ⟨ht0, L, hL, htL⟩, rfl⟩
  exact statStrength_le_of_local hq hμ ht0 hL htL

/-- **Theorem F.2, (F.8).** For every no-signalling behaviour and every input law,
`S_μ(q) ≤ [1 - LF(q)] Ξ(μ) ≤ Ξ(μ)`. -/
theorem statistical_ceiling_spec {q : Table α β} (hq : IsNoSignalling q)
    {μ : Fin 2 → Fin 2 → ℝ} (hμ : ∀ x y, 0 ≤ μ x y) (hμ1 : ∑ x, ∑ y, μ x y = 1) :
    statStrength μ q ≤ ENNReal.ofReal (1 - localFraction q) * xiMin μ ∧
      ENNReal.ofReal (1 - localFraction q) * xiMin μ ≤ xiMin μ :=
  ⟨statStrength_le_localFraction hq hμ hμ1,
    mul_le_of_le_one_left (zero_le)
      (ENNReal.ofReal_le_one.mpr (by linarith [localFraction_nonneg hq]))⟩

end

end CGLMPBounds
