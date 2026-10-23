module

public import CGLMPBounds.Scenario.Local
public import CGLMPBounds.CGLMP.LocalBound
public import CGLMPBounds.Fourier.LocalWeight

@[expose] public section


/-!
# The local component `L_d` of Lemma F.1

Manuscript locator: Appendix F.1, construction before Lemma F.1: "Construct `L_d` by choosing an
edge uniformly, putting residual `d - 1` on that edge and zero on the other three, and choosing
`a₀` uniformly. The remaining outcomes are `b₀ = a₀ - r₀₀`, `a₁ = b₀ - r₁₀`, `b₁ = a₁ - r₁₁`. ...
This gives `4d` deterministic strategies of weight `1/(4d)`. Every edge has residual probabilities
`3/4, 1/4` at `0, d - 1`, and all marginals are uniform." Lemma F.1: `Q_d ≥ a_d L_d`, and `a_d` is
maximal for this `L_d`.

Here the Fourier-phase behaviour is represented by its closed formula `f_d(r_{xy}) / d` from (F.1);
deriving (F.1) from the measurements (B.2) is a separate claim.

* `localComponent_mem_localSet` : `L_d` is Bell-local;
* `localComponent_apply` : its entries, through the oriented difference `δ_{xy}(a,b)` with
  `r_{xy} = [δ_{xy}]_d` (`residual_eq_val`);
* `sum_localComponent_right`, `sum_localComponent_left` : uniform marginals;
* `localWeight_mul_localComponent_le` : `a_d L_d ≤ f_d(r) / d` entrywise (`d ≥ 2`);
* `le_localWeight_of_le` : no larger multiple of `L_d` fits below `f_d(r) / d`.
-/

namespace CGLMPBounds

noncomputable section

variable (d : ℕ) [NeZero d]

/-! ### Oriented differences -/

/-- The oriented difference `δ_{xy}(a,b) ∈ ℤ_d` whose reduction is the residual `r_{xy}` of (B.1):
`δ₀₀ = a - b`, `δ₁₀ = b - a`, `δ₁₁ = a - b`, `δ₀₁ = b - a - 1`. -/
def orientedDiff (x y : Fin 2) (a b : ZMod d) : ZMod d :=
  if x = y then a - b else if x = 1 then b - a else b - a - 1

theorem residual_eq_val (x y : Fin 2) (a b : ZMod d) :
    residual d x y a b = (orientedDiff d x y a b).val := by
  unfold residual orientedDiff
  split_ifs <;> rfl

theorem orientedDiff_zero_zero (a b : ZMod d) : orientedDiff d 0 0 a b = a - b := rfl

theorem orientedDiff_one_zero (a b : ZMod d) : orientedDiff d 1 0 a b = b - a := rfl

theorem orientedDiff_one_one (a b : ZMod d) : orientedDiff d 1 1 a b = a - b := rfl

theorem orientedDiff_zero_one (a b : ZMod d) : orientedDiff d 0 1 a b = b - a - 1 := rfl

/-- Oriented differences only depend on `a - b`. -/
theorem orientedDiff_eq_iff :
    ∀ (x y : Fin 2) (a b A B : ZMod d),
      orientedDiff d x y a b = orientedDiff d x y A B ↔ a - A = b - B := by
  refine Fin.forall_fin_two.mpr ⟨Fin.forall_fin_two.mpr ⟨?_, ?_⟩, Fin.forall_fin_two.mpr ⟨?_, ?_⟩⟩
  · intro a b A B
    simp only [orientedDiff_zero_zero]
    constructor <;> intro h <;> linear_combination h
  · intro a b A B
    simp only [orientedDiff_zero_one]
    constructor <;> intro h <;> linear_combination (-1 : ZMod d) * h
  · intro a b A B
    simp only [orientedDiff_one_zero]
    constructor <;> intro h <;> linear_combination (-1 : ZMod d) * h
  · intro a b A B
    simp only [orientedDiff_one_one]
    constructor <;> intro h <;> linear_combination h

/-- For a fixed outcome of Alice, Bob's outcome ↦ `δ_{xy}(a, b)` is a bijection of `ℤ_d`. -/
theorem sum_orientedDiff_right (g : ZMod d → ℝ) (x y : Fin 2) (a : ZMod d) :
    ∑ b : ZMod d, g (orientedDiff d x y a b) = ∑ c : ZMod d, g c := by
  unfold orientedDiff
  split_ifs
  · exact Fintype.sum_equiv (Equiv.subLeft a) _ _ (fun _ => rfl)
  · exact Fintype.sum_equiv (Equiv.subRight a) _ _ (fun _ => rfl)
  · exact Fintype.sum_equiv ((Equiv.subRight a).trans (Equiv.subRight 1)) _ _ (fun _ => rfl)

/-- For a fixed outcome of Bob, Alice's outcome ↦ `δ_{xy}(a, b)` is a bijection of `ℤ_d`. -/
theorem sum_orientedDiff_left (g : ZMod d → ℝ) (x y : Fin 2) (b : ZMod d) :
    ∑ a : ZMod d, g (orientedDiff d x y a b) = ∑ c : ZMod d, g c := by
  unfold orientedDiff
  split_ifs
  · exact Fintype.sum_equiv (Equiv.subRight b) _ _ (fun _ => rfl)
  · exact Fintype.sum_equiv (Equiv.subLeft b) _ _ (fun _ => rfl)
  · exact Fintype.sum_equiv ((Equiv.subLeft b).trans (Equiv.subRight 1)) _ _ (fun _ => rfl)

theorem zmod_val_eq_sub_one_iff (u : ZMod d) : u.val = d - 1 ↔ u = -1 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne d)
  have h : (-1 : ZMod (n.succ)).val = n.succ - 1 := by
    rw [ZMod.val_neg_one n, Nat.succ_sub_one]
  constructor
  · intro hu
    exact ZMod.val_injective _ (hu.trans h.symm)
  · intro hu
    rw [hu, h]

theorem neg_one_ne_zero_of_two_le (hd : 2 ≤ d) : (-1 : ZMod d) ≠ 0 := by
  intro h
  have h1 : (-1 : ZMod d).val = d - 1 := (zmod_val_eq_sub_one_iff d _).mpr rfl
  rw [h, ZMod.val_zero] at h1
  omega

/-! ### Residual patterns and their strategies -/

/-- The residual pattern of the construction: `-1` (residual `d - 1`) on the edge `e`, `0` on the
other three contexts. -/
def edgePattern (e : Fin 2 × Fin 2) (x y : Fin 2) : ZMod d :=
  if (x, y) = e then -1 else 0

theorem edgePattern_apply (e : Fin 2 × Fin 2) (x y : Fin 2) :
    edgePattern d e x y = if (x, y) = e then -1 else 0 :=
  rfl

/-- The four values of a residual pattern sum to `-1`, as for every deterministic assignment. -/
theorem edgePattern_sum (e : Fin 2 × Fin 2) :
    edgePattern d e 0 0 + edgePattern d e 1 0 + edgePattern d e 1 1 + edgePattern d e 0 1 = -1 := by
  have h : ∑ p : Fin 2 × Fin 2, (if p = e then (-1 : ZMod d) else 0) = -1 := by
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ e)]
  rw [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two] at h
  simp only [edgePattern_apply]
  linear_combination h

/-- Alice's outputs relative to the anchor `a₀`: `a₀ - a₀ = 0`, `a₁ - a₀ = -r₀₀ - r₁₀`. -/
def patternOffsetA (ρ : Fin 2 → Fin 2 → ZMod d) (x : Fin 2) : ZMod d :=
  if x = 0 then 0 else -ρ 0 0 - ρ 1 0

/-- Bob's outputs relative to the anchor `a₀`: `b₀ - a₀ = -r₀₀`, `b₁ - a₀ = -r₀₀ - r₁₀ - r₁₁`. -/
def patternOffsetB (ρ : Fin 2 → Fin 2 → ZMod d) (y : Fin 2) : ZMod d :=
  if y = 0 then -ρ 0 0 else -ρ 0 0 - ρ 1 0 - ρ 1 1

theorem patternOffsetA_zero (ρ : Fin 2 → Fin 2 → ZMod d) : patternOffsetA d ρ 0 = 0 := rfl

theorem patternOffsetA_one (ρ : Fin 2 → Fin 2 → ZMod d) :
    patternOffsetA d ρ 1 = -ρ 0 0 - ρ 1 0 := rfl

theorem patternOffsetB_zero (ρ : Fin 2 → Fin 2 → ZMod d) : patternOffsetB d ρ 0 = -ρ 0 0 := rfl

theorem patternOffsetB_one (ρ : Fin 2 → Fin 2 → ZMod d) :
    patternOffsetB d ρ 1 = -ρ 0 0 - ρ 1 0 - ρ 1 1 := rfl

/-- The deterministic strategy with anchor `a₀ = l` and residual pattern `ρ`:
`b₀ = a₀ - ρ₀₀`, `a₁ = b₀ - ρ₁₀`, `b₁ = a₁ - ρ₁₁`. -/
def patternStrategy (ρ : Fin 2 → Fin 2 → ZMod d) (l : ZMod d) : Strategy (ZMod d) (ZMod d) :=
  (fun x => l + patternOffsetA d ρ x, fun y => l + patternOffsetB d ρ y)

/-- The strategy realises the pattern when its four values sum to `-1`. -/
theorem orientedDiff_patternOffset (ρ : Fin 2 → Fin 2 → ZMod d)
    (hρ : ρ 0 0 + ρ 1 0 + ρ 1 1 + ρ 0 1 = -1) :
    ∀ x y : Fin 2, orientedDiff d x y (patternOffsetA d ρ x) (patternOffsetB d ρ y) = ρ x y := by
  refine Fin.forall_fin_two.mpr ⟨Fin.forall_fin_two.mpr ⟨?_, ?_⟩, Fin.forall_fin_two.mpr ⟨?_, ?_⟩⟩
  · rw [orientedDiff_zero_zero, patternOffsetA_zero, patternOffsetB_zero]
    ring
  · rw [orientedDiff_zero_one, patternOffsetA_zero, patternOffsetB_one]
    linear_combination (-1 : ZMod d) * hρ
  · rw [orientedDiff_one_zero, patternOffsetA_one, patternOffsetB_zero]
    ring
  · rw [orientedDiff_one_one, patternOffsetA_one, patternOffsetB_one]
    ring

/-! ### The component `L_d` -/

/-- The local component `L_d` of Lemma F.1: the uniform mixture, over the four edges `e` and the
anchor `l ∈ ℤ_d`, of the deterministic strategies with residual `d - 1` on `e` and `0` elsewhere. -/
def localComponent : Table (ZMod d) (ZMod d) :=
  ∑ e : Fin 2 × Fin 2, ∑ l : ZMod d,
    (1 / (4 * (d : ℝ))) • detTable (patternStrategy d (edgePattern d e) l)

theorem localComponent_mem_localSet : localComponent d ∈ localSet (ZMod d) (ZMod d) := by
  have hd : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  have h4 : (4 * (d : ℝ)) ≠ 0 := mul_ne_zero (by norm_num) hd
  have hc : (0 : ℝ) ≤ 1 / (4 * (d : ℝ)) :=
    div_nonneg zero_le_one (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
  have hcard : ((Fintype.card ((Fin 2 × Fin 2) × ZMod d) : ℕ) : ℝ) = 4 * (d : ℝ) := by
    simp only [Fintype.card_prod, Fintype.card_fin, ZMod.card, Nat.cast_mul, Nat.cast_ofNat] <;>
      ring
  have hsum : ∑ _p : (Fin 2 × Fin 2) × ZMod d, (1 / (4 * (d : ℝ))) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard, mul_one_div, div_self h4]
  have hEq : localComponent d = ∑ p : (Fin 2 × Fin 2) × ZMod d,
      (1 / (4 * (d : ℝ))) • detTable (patternStrategy d (edgePattern d p.1) p.2) :=
    (Fintype.sum_prod_type' (fun e l => (1 / (4 * (d : ℝ))) •
      detTable (patternStrategy d (edgePattern d e) l))).symm
  rw [hEq]
  exact (convex_convexHull ℝ _).sum_mem (fun _ _ => hc) hsum
    (fun p _ => subset_convexHull ℝ _ ⟨_, rfl⟩)

/-- Summing over the anchor: exactly one anchor fits, and only when `a - A = b - B`. -/
theorem sum_anchor (A B a b : ZMod d) :
    ∑ l : ZMod d, (if a = l + A ∧ b = l + B then (1 : ℝ) else 0)
      = if a - A = b - B then 1 else 0 := by
  rw [Finset.sum_eq_single_of_mem (a - A) (Finset.mem_univ _)]
  · by_cases h : a - A = b - B
    · have hc : a = a - A + A ∧ b = a - A + B :=
        ⟨by ring, by linear_combination (-1 : ZMod d) * h⟩
      rw [if_pos hc, if_pos h]
    · have hc : ¬(a = a - A + A ∧ b = a - A + B) := by
        rintro ⟨_, h2⟩
        exact h (by linear_combination (-1 : ZMod d) * h2)
      rw [if_neg hc, if_neg h]
  · intro l _ hl
    have hc : ¬(a = l + A ∧ b = l + B) := by
      rintro ⟨h1, _⟩
      exact hl (by linear_combination (-1 : ZMod d) * h1)
    rw [if_neg hc]

theorem ite_eq_ite_pattern (δ : ZMod d) (c : Prop) [Decidable c] :
    (if δ = (if c then -1 else 0) then (1 : ℝ) else 0)
      = if c then (if δ = -1 then 1 else 0) else (if δ = 0 then 1 else 0) := by
  by_cases h : c
  · simp only [if_pos h]
  · simp only [if_neg h]

/-- The contribution of one edge to an entry of `L_d`, after summing over the anchor. -/
theorem sum_anchor_edge (x y : Fin 2) (a b : ZMod d) (e : Fin 2 × Fin 2) :
    ∑ l : ZMod d, (if a = l + patternOffsetA d (edgePattern d e) x
        ∧ b = l + patternOffsetB d (edgePattern d e) y then (1 : ℝ) else 0)
      = if (x, y) = e then (if orientedDiff d x y a b = -1 then 1 else 0)
        else (if orientedDiff d x y a b = 0 then 1 else 0) := by
  have key : (a - patternOffsetA d (edgePattern d e) x = b - patternOffsetB d (edgePattern d e) y)
      ↔ orientedDiff d x y a b = (if (x, y) = e then -1 else 0) := by
    rw [← edgePattern_apply,
      ← orientedDiff_patternOffset d (edgePattern d e) (edgePattern_sum d e) x y]
    exact (orientedDiff_eq_iff d x y a b _ _).symm
  rw [sum_anchor, ← ite_eq_ite_pattern]
  exact if_congr key rfl rfl

/-- Summing a context-indicator over the four edges: one edge matches, three do not. -/
theorem sum_ite_context (x y : Fin 2) (P K : ℝ) :
    ∑ e : Fin 2 × Fin 2, (if (x, y) = e then P else K) = P + 3 * K := by
  have h : ∀ e : Fin 2 × Fin 2,
      (if (x, y) = e then P else K) = (if (x, y) = e then P - K else 0) + K := by
    intro e
    by_cases he : (x, y) = e
    · rw [if_pos he, if_pos he]
      ring
    · rw [if_neg he, if_neg he]
      ring
  rw [Finset.sum_congr rfl (fun e _ => h e), Finset.sum_add_distrib, Finset.sum_ite_eq,
    if_pos (Finset.mem_univ _), Finset.sum_const, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

/-- Entries of `L_d`: probability `3/(4d)` when `r_{xy} = 0`, `1/(4d)` when `r_{xy} = d - 1`. -/
theorem localComponent_apply (x y : Fin 2) (a b : ZMod d) :
    localComponent d x y a b
      = 1 / (4 * (d : ℝ)) * ((if orientedDiff d x y a b = -1 then 1 else 0)
          + 3 * (if orientedDiff d x y a b = 0 then 1 else 0)) := by
  have step1 : localComponent d x y a b = 1 / (4 * (d : ℝ)) * ∑ e : Fin 2 × Fin 2, ∑ l : ZMod d,
      (if a = l + patternOffsetA d (edgePattern d e) x
          ∧ b = l + patternOffsetB d (edgePattern d e) y then (1 : ℝ) else 0) := by
    simp only [localComponent, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, detTable,
      patternStrategy]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    rw [Finset.mul_sum]
  rw [step1, Finset.sum_congr rfl (fun e _ => sum_anchor_edge d x y a b e), sum_ite_context]

theorem sum_profile :
    ∑ c : ZMod d, 1 / (4 * (d : ℝ)) * ((if c = -1 then (1 : ℝ) else 0)
        + 3 * (if c = 0 then 1 else 0)) = 1 / (d : ℝ) := by
  have e4 : (1 : ℝ) / (4 * (d : ℝ)) = 1 / 4 * (1 / (d : ℝ)) := by
    rw [div_mul_div_comm, one_mul]
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq',
    Finset.sum_ite_eq', if_pos (Finset.mem_univ _), if_pos (Finset.mem_univ _), e4]
  ring

/-- Alice's marginal of `L_d` is uniform. -/
theorem sum_localComponent_right (x y : Fin 2) (a : ZMod d) :
    ∑ b : ZMod d, localComponent d x y a b = 1 / (d : ℝ) := by
  rw [Finset.sum_congr rfl (fun b _ => localComponent_apply d x y a b),
    sum_orientedDiff_right d (fun c => 1 / (4 * (d : ℝ)) * ((if c = -1 then (1 : ℝ) else 0)
      + 3 * (if c = 0 then 1 else 0))) x y a]
  exact sum_profile d

/-- Bob's marginal of `L_d` is uniform. -/
theorem sum_localComponent_left (x y : Fin 2) (b : ZMod d) :
    ∑ a : ZMod d, localComponent d x y a b = 1 / (d : ℝ) := by
  rw [Finset.sum_congr rfl (fun a _ => localComponent_apply d x y a b),
    sum_orientedDiff_left d (fun c => 1 / (4 * (d : ℝ)) * ((if c = -1 then (1 : ℝ) else 0)
      + 3 * (if c = 0 then 1 else 0))) x y b]
  exact sum_profile d

/-! ### Domination by the Fourier-phase residual law -/

theorem fourierResidualLaw_nonneg (r : ℕ) : 0 ≤ fourierResidualLaw d r := by
  unfold fourierResidualLaw
  positivity

/-- Equation (F.2), entrywise, for the closed formula (F.1): `a_d L_d ≤ f_d(r_{xy}) / d`. -/
theorem localWeight_mul_localComponent_le (hd : 2 ≤ d) (x y : Fin 2) (a b : ZMod d) :
    localWeight d * localComponent d x y a b
      ≤ fourierResidualLaw d (residual d x y a b) / (d : ℝ) := by
  have e4 : (1 : ℝ) / (4 * (d : ℝ)) = 1 / 4 * (1 / (d : ℝ)) := by
    rw [div_mul_div_comm, one_mul]
  have ht : (0 : ℝ) ≤ 1 / (d : ℝ) := div_nonneg zero_le_one (Nat.cast_nonneg _)
  rw [localComponent_apply, residual_eq_val, e4,
    div_eq_mul_one_div (fourierResidualLaw d (orientedDiff d x y a b).val) (d : ℝ)]
  by_cases h1 : orientedDiff d x y a b = -1
  · have h0 : orientedDiff d x y a b ≠ 0 := by
      rw [h1]
      exact neg_one_ne_zero_of_two_le d hd
    rw [if_pos h1, if_neg h0, (zmod_val_eq_sub_one_iff d _).mpr h1, localWeight_eq_four_mul d hd]
    apply le_of_eq
    ring
  · rw [if_neg h1]
    by_cases h0 : orientedDiff d x y a b = 0
    · rw [if_pos h0, h0, ZMod.val_zero, localWeight_eq_four_mul d hd]
      have h3 := three_mul_fourierResidualLaw_le d hd
      linarith [mul_le_mul_of_nonneg_right h3 ht]
    · rw [if_neg h0]
      have hf := fourierResidualLaw_nonneg d (orientedDiff d x y a b).val
      linarith [mul_nonneg hf ht]

/-- The weight `a_d` is maximal for `L_d` (Lemma F.1): the residual-`(d-1)` entries are tight. -/
theorem le_localWeight_of_le (hd : 2 ≤ d) {α : ℝ}
    (h : ∀ x y a b, α * localComponent d x y a b
      ≤ fourierResidualLaw d (residual d x y a b) / (d : ℝ)) :
    α ≤ localWeight d := by
  have hdpos : (0 : ℝ) < d := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have ht : (0 : ℝ) < 1 / (d : ℝ) := div_pos one_pos hdpos
  have e4 : (1 : ℝ) / (4 * (d : ℝ)) = 1 / 4 * (1 / (d : ℝ)) := by
    rw [div_mul_div_comm, one_mul]
  have h1 : orientedDiff d 0 0 0 1 = -1 := by
    rw [orientedDiff_zero_zero, zero_sub]
  have h0 : orientedDiff d 0 0 0 1 ≠ 0 := by
    rw [h1]
    exact neg_one_ne_zero_of_two_le d hd
  have hspec := h 0 0 0 1
  rw [localComponent_apply, if_pos h1, if_neg h0, residual_eq_val,
    (zmod_val_eq_sub_one_iff d _).mpr h1, e4,
    div_eq_mul_one_div (fourierResidualLaw d (d - 1)) (d : ℝ)] at hspec
  rw [localWeight_eq_four_mul d hd]
  by_contra hc
  have hlt := mul_lt_mul_of_pos_right (not_le.mp hc) ht
  linarith

end

end CGLMPBounds
