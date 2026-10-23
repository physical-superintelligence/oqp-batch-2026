module

public import CGLMPBounds.Defs.StatisticalConstants
public import CGLMPBounds.Defs.Statistics

@[expose] public section


/-!
# The four-variable minimum `Ξ(μ)` (Theorem F.2)

Supplement, Theorem F.2: "If some `μ_e = 0`, then `Ξ(μ) = 0`. For full-support `μ`, there is a
unique `λ > 0` satisfying `Σ_e min{1, μ_e/λ} = 3`, and `Ξ(μ) = Σ_{μ_e<λ} μ_e log₂(λ/μ_e)` (F.9).
Moreover, `Ξ(μ) ≤ c_KL := log₂(4/3)`, with equality exactly for uniform inputs."

* `xiMin_le`, `le_xiMin`, `obj_eq_ofReal`, `sum_mul_neg_logb` : handling of the infimum (B.6);
* `xiMin_eq_zero_of_absent` : `Ξ(μ) = 0` if some `μ_e = 0`;
* `xiMin_le_cKL` : `Ξ(μ) ≤ log₂(4/3)` (the point `s_e = 3/4`);
* `xiMin_lt_cKL`, `xiMin_eq_cKL_iff` : equality exactly for uniform inputs (for nonuniform `μ` the
  explicit point `s_e = (2 + μ_e)/3` is strictly better);
* `exists_unique_xiLam`, `xiMin_closed_form`, `xi_closed_form_spec` : the closed form (F.9), by the
  tangent-line inequality for `-log` at the candidate optimiser `s_e = min{1, μ_e/λ}`.
-/

namespace CGLMPBounds

noncomputable section

open scoped ENNReal

theorem cKL_eq_neg : cKL = -Real.logb 2 (3 / 4) := by
  rw [cKL, ← Real.logb_inv]
  norm_num

theorem cKL_pos : 0 < cKL := Real.logb_pos (by norm_num) (by norm_num)

theorem negLogTwo_of_ne_zero {s : ℝ} (hs : s ≠ 0) :
    negLogTwo s = ENNReal.ofReal (-Real.logb 2 s) := by
  rw [negLogTwo, if_neg hs]

theorem negLogTwo_zero : negLogTwo 0 = ∞ := by
  rw [negLogTwo, if_pos rfl]

theorem xiMin_le {μ s : Fin 2 → Fin 2 → ℝ} (hs : ∀ x y, 0 ≤ s x y ∧ s x y ≤ 1)
    (h3 : ∑ x, ∑ y, s x y = 3) :
    xiMin μ ≤ ∑ x, ∑ y, ENNReal.ofReal (μ x y) * negLogTwo (s x y) := by
  unfold xiMin
  exact iInf₂_le s ⟨hs, h3⟩

theorem le_xiMin {μ : Fin 2 → Fin 2 → ℝ} {B : ℝ≥0∞}
    (h : ∀ s : Fin 2 → Fin 2 → ℝ, (∀ x y, 0 ≤ s x y ∧ s x y ≤ 1) → ∑ x, ∑ y, s x y = 3 →
      B ≤ ∑ x, ∑ y, ENNReal.ofReal (μ x y) * negLogTwo (s x y)) : B ≤ xiMin μ := by
  unfold xiMin
  exact le_iInf₂ (fun s hs => h s hs.1 hs.2)

/-- At a point with positive coordinates the objective of (B.6) is a finite real number. -/
theorem obj_eq_ofReal {μ s : Fin 2 → Fin 2 → ℝ} (hμ : ∀ x y, 0 ≤ μ x y)
    (hs : ∀ x y, 0 < s x y ∧ s x y ≤ 1) :
    ∑ x, ∑ y, ENNReal.ofReal (μ x y) * negLogTwo (s x y)
      = ENNReal.ofReal (∑ x, ∑ y, μ x y * -Real.logb 2 (s x y)) := by
  have hterm : ∀ x y, 0 ≤ μ x y * -Real.logb 2 (s x y) := fun x y =>
    mul_nonneg (hμ x y) (neg_nonneg.mpr (Real.logb_nonpos (by norm_num) (hs x y).1.le (hs x y).2))
  rw [ENNReal.ofReal_sum_of_nonneg (fun x _ => Finset.sum_nonneg (fun y _ => hterm x y))]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [ENNReal.ofReal_sum_of_nonneg (fun y _ => hterm x y)]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [negLogTwo_of_ne_zero (hs x y).1.ne', ENNReal.ofReal_mul (hμ x y)]

theorem sum_mul_neg_logb (w s : Fin 2 → Fin 2 → ℝ) :
    ∑ x, ∑ y, w x y * -Real.logb 2 (s x y)
      = (∑ x, ∑ y, w x y * -Real.log (s x y)) / Real.log 2 := by
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  unfold Real.logb
  ring

/-- A zero coordinate of `s` makes the objective infinite when the input pair is present. -/
theorem obj_eq_top {μ s : Fin 2 → Fin 2 → ℝ} {x y : Fin 2} (hμ : 0 < μ x y) (hs : s x y = 0) :
    ∑ x', ∑ y', ENNReal.ofReal (μ x' y') * negLogTwo (s x' y') = ∞ := by
  have htop : ENNReal.ofReal (μ x y) * negLogTwo (s x y) = ∞ := by
    rw [hs, negLogTwo_zero, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hμ).ne']
  have hle : ENNReal.ofReal (μ x y) * negLogTwo (s x y)
      ≤ ∑ x', ∑ y', ENNReal.ofReal (μ x' y') * negLogTwo (s x' y') :=
    (Finset.single_le_sum (f := fun y' => ENNReal.ofReal (μ x y') * negLogTwo (s x y'))
      (fun _ _ => zero_le) (Finset.mem_univ y)).trans
    (Finset.single_le_sum (f := fun x' => ∑ y', ENNReal.ofReal (μ x' y') * negLogTwo (s x' y'))
      (fun _ _ => zero_le) (Finset.mem_univ x))
  rw [htop] at hle
  exact top_le_iff.mp hle

/-! ### The zero case and the bound `Ξ(μ) ≤ log₂(4/3)` -/

/-- Theorem F.2: if some input pair is absent, then `Ξ(μ) = 0`. -/
theorem xiMin_eq_zero_of_absent {μ : Fin 2 → Fin 2 → ℝ} {x₀ y₀ : Fin 2} (h0 : μ x₀ y₀ = 0) :
    xiMin μ = 0 := by
  refine le_antisymm ?_ (zero_le)
  have hs : ∀ x y, 0 ≤ (if x = x₀ ∧ y = y₀ then (0 : ℝ) else 1) ∧
      (if x = x₀ ∧ y = y₀ then (0 : ℝ) else 1) ≤ 1 := by
    intro x y
    by_cases h : x = x₀ ∧ y = y₀ <;> simp [h]
  have h3 : ∑ x, ∑ y, (if x = x₀ ∧ y = y₀ then (0 : ℝ) else 1) = 3 := by
    fin_cases x₀ <;> fin_cases y₀ <;> simp [Fin.sum_univ_two] <;> norm_num
  refine (xiMin_le (s := fun x y => if x = x₀ ∧ y = y₀ then (0 : ℝ) else 1) hs h3).trans
    (le_of_eq ?_)
  refine Finset.sum_eq_zero (fun x _ => Finset.sum_eq_zero (fun y _ => ?_))
  by_cases h : x = x₀ ∧ y = y₀
  · rw [h.1, h.2, h0, ENNReal.ofReal_zero, zero_mul]
  · show ENNReal.ofReal (μ x y) * negLogTwo (if x = x₀ ∧ y = y₀ then (0 : ℝ) else 1) = 0
    rw [if_neg h, negLogTwo_of_ne_zero one_ne_zero, Real.logb_one, neg_zero, ENNReal.ofReal_zero,
      mul_zero]

/-- Theorem F.2: `Ξ(μ) ≤ c_KL = log₂(4/3)` (take `s_e = 3/4`). -/
theorem xiMin_le_cKL {μ : Fin 2 → Fin 2 → ℝ} (hμ : ∀ x y, 0 ≤ μ x y)
    (hμ1 : ∑ x, ∑ y, μ x y = 1) : xiMin μ ≤ ENNReal.ofReal cKL := by
  have hs : ∀ x y : Fin 2, 0 < (3 / 4 : ℝ) ∧ (3 / 4 : ℝ) ≤ 1 := fun _ _ =>
    ⟨by norm_num, by norm_num⟩
  have h3 : ∑ _x : Fin 2, ∑ _y : Fin 2, (3 / 4 : ℝ) = 3 := by norm_num
  refine (xiMin_le (s := fun _ _ => 3 / 4) (fun x y => ⟨(hs x y).1.le, (hs x y).2⟩) h3).trans
    (le_of_eq ?_)
  rw [obj_eq_ofReal (s := fun _ _ => 3 / 4) hμ hs, cKL_eq_neg]
  congr 1
  simp only [← Finset.sum_mul, hμ1, one_mul]

theorem xiMin_ne_top {μ : Fin 2 → Fin 2 → ℝ} (hμ : ∀ x y, 0 ≤ μ x y)
    (hμ1 : ∑ x, ∑ y, μ x y = 1) : xiMin μ ≠ ∞ :=
  ((xiMin_le_cKL hμ hμ1).trans_lt ENNReal.ofReal_lt_top).ne

/-- For uniform inputs every feasible point has objective at least `log₂(4/3)`. -/
theorem cKL_le_obj_uniform {s : Fin 2 → Fin 2 → ℝ} (hs : ∀ x y, 0 ≤ s x y ∧ s x y ≤ 1)
    (h3 : ∑ x, ∑ y, s x y = 3) :
    ENNReal.ofReal cKL ≤ ∑ x, ∑ y, ENNReal.ofReal (1 / 4) * negLogTwo (s x y) := by
  by_cases hz : ∃ x y, s x y = 0
  · obtain ⟨x, y, hxy⟩ := hz
    rw [obj_eq_top (μ := fun _ _ => 1 / 4) (x := x) (y := y) (by norm_num) hxy]
    exact le_top
  · push_neg at hz
    have hpos : ∀ x y, 0 < s x y ∧ s x y ≤ 1 := fun x y =>
      ⟨lt_of_le_of_ne (hs x y).1 (Ne.symm (hz x y)), (hs x y).2⟩
    rw [obj_eq_ofReal (μ := fun _ _ => 1 / 4) (s := s) (fun _ _ => by norm_num) hpos]
    apply ENNReal.ofReal_le_ofReal
    rw [sum_mul_neg_logb]
    unfold cKL Real.logb
    refine div_le_div_of_nonneg_right ?_ (Real.log_pos (by norm_num)).le
    have key : ∀ x y, Real.log (s x y) ≤ Real.log (3 / 4) + 4 / 3 * s x y - 1 := by
      intro x y
      have h := Real.log_le_sub_one_of_pos (div_pos (hpos x y).1 (by norm_num : (0 : ℝ) < 3 / 4))
      rw [Real.log_div (hpos x y).1.ne' (by norm_num : (3 / 4 : ℝ) ≠ 0)] at h
      have e : s x y / (3 / 4) = 4 / 3 * s x y := by ring
      rw [e] at h
      linarith
    have hl : Real.log (4 / 3) = -Real.log (3 / 4) := by
      rw [← Real.log_inv]
      norm_num
    have k00 := key 0 0
    have k01 := key 0 1
    have k10 := key 1 0
    have k11 := key 1 1
    simp only [Fin.sum_univ_two] at h3 ⊢
    linarith

/-- Auxiliary nonnegative terms in the strict inequality `Ξ(μ) < c_KL` for nonuniform `μ`. -/
def xiGap (μ : Fin 2 → Fin 2 → ℝ) (x y : Fin 2) : ℝ :=
  32 / 81 * (4 / 3 * ((2 + μ x y) / 3))⁻¹ * (μ x y - 1 / 4) ^ 2

/-- For a nonuniform input law, `Ξ(μ) < log₂(4/3)`: the feasible point `s_e = (2 + μ_e)/3` (a
step from `3/4` in the direction `μ - 1/4`) has objective at most
`log₂(4/3) - Σ_e xiGap μ e / ln 2`. -/
theorem xiMin_lt_cKL {μ : Fin 2 → Fin 2 → ℝ} (hμ : ∀ x y, 0 ≤ μ x y)
    (hμ1 : ∑ x, ∑ y, μ x y = 1) (hne : ¬∀ x y, μ x y = 1 / 4) :
    xiMin μ < ENNReal.ofReal cKL := by
  have hμle : ∀ x y, μ x y ≤ 1 := by
    intro x y
    have h1 : μ x y ≤ ∑ y', μ x y' :=
      Finset.single_le_sum (f := fun y' => μ x y') (fun y' _ => hμ x y') (Finset.mem_univ y)
    have h2 : ∑ y', μ x y' ≤ ∑ x', ∑ y', μ x' y' :=
      Finset.single_le_sum (f := fun x' => ∑ y', μ x' y')
        (fun x' _ => Finset.sum_nonneg (fun y' _ => hμ x' y')) (Finset.mem_univ x)
    linarith
  have hs : ∀ x y, 0 < (2 + μ x y) / 3 ∧ (2 + μ x y) / 3 ≤ 1 := fun x y =>
    ⟨by linarith [hμ x y], by linarith [hμle x y]⟩
  have h3 : ∑ x, ∑ y, (2 + μ x y) / 3 = 3 := by
    simp only [Fin.sum_univ_two] at hμ1 ⊢
    linarith
  refine (xiMin_le (s := fun x y => (2 + μ x y) / 3)
    (fun x y => ⟨(hs x y).1.le, (hs x y).2⟩) h3).trans_lt ?_
  rw [obj_eq_ofReal (s := fun x y => (2 + μ x y) / 3) hμ hs]
  refine (ENNReal.ofReal_lt_ofReal_iff cKL_pos).mpr ?_
  rw [sum_mul_neg_logb]
  unfold cKL Real.logb
  refine div_lt_div_of_pos_right ?_ (Real.log_pos (by norm_num))
  have term : ∀ x y, μ x y * -Real.log ((2 + μ x y) / 3)
      ≤ μ x y * Real.log (4 / 3) - (1 / 9 * (μ x y - 1 / 4) + xiGap μ x y) := by
    intro x y
    have hpos : 0 < 4 / 3 * ((2 + μ x y) / 3) := by linarith [hμ x y]
    have hl := Real.one_sub_inv_le_log_of_pos hpos
    rw [Real.log_mul (by norm_num : (4 / 3 : ℝ) ≠ 0) (hs x y).1.ne'] at hl
    have hu : (4 / 3 * ((2 + μ x y) / 3))⁻¹ * (8 + 4 * μ x y) = 9 := by
      have h1 : (4 / 3 * ((2 + μ x y) / 3))⁻¹ * (4 / 3 * ((2 + μ x y) / 3)) = 1 :=
        inv_mul_cancel₀ hpos.ne'
      linear_combination 9 * h1
    have hid : μ x y * (1 - (4 / 3 * ((2 + μ x y) / 3))⁻¹)
        = 1 / 9 * (μ x y - 1 / 4) + xiGap μ x y := by
      unfold xiGap
      linear_combination (-(8 * μ x y + 1 / 4) / 81) * hu
    have hmul := mul_le_mul_of_nonneg_left hl (hμ x y)
    rw [hid, mul_add] at hmul
    rw [mul_neg]
    linarith
  have hsum : ∑ x, ∑ y, μ x y * -Real.log ((2 + μ x y) / 3)
      ≤ ∑ x, ∑ y, (μ x y * Real.log (4 / 3) - (1 / 9 * (μ x y - 1 / 4) + xiGap μ x y)) :=
    Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun y _ => term x y))
  have hgap : ∀ x y, 0 ≤ xiGap μ x y := fun x y => by
    unfold xiGap
    exact mul_nonneg (mul_nonneg (by norm_num) (inv_nonneg.mpr (by linarith [hμ x y])))
      (sq_nonneg _)
  obtain ⟨x0, y0, h0⟩ : ∃ x y, μ x y ≠ 1 / 4 := by
    push_neg at hne
    exact hne
  have hgap0 : 0 < xiGap μ x0 y0 := by
    unfold xiGap
    exact mul_pos (mul_pos (by norm_num) (inv_pos.mpr (by linarith [hμ x0 y0])))
      (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (sub_ne_zero.mpr h0))))
  have hgsum : xiGap μ x0 y0 ≤ ∑ x, ∑ y, xiGap μ x y :=
    (Finset.single_le_sum (f := fun y => xiGap μ x0 y) (fun y _ => hgap x0 y)
      (Finset.mem_univ y0)).trans
    (Finset.single_le_sum (f := fun x => ∑ y, xiGap μ x y)
      (fun x _ => Finset.sum_nonneg (fun y _ => hgap x y)) (Finset.mem_univ x0))
  have hL : μ 0 0 * Real.log (4 / 3) + μ 0 1 * Real.log (4 / 3)
      + (μ 1 0 * Real.log (4 / 3) + μ 1 1 * Real.log (4 / 3)) = Real.log (4 / 3) := by
    simp only [Fin.sum_univ_two] at hμ1
    rw [← add_mul, ← add_mul, ← add_mul, hμ1, one_mul]
  simp only [Fin.sum_univ_two] at hsum hgsum hμ1 ⊢
  linarith

/-- Theorem F.2: `Ξ(μ) = log₂(4/3)` exactly for uniform inputs. -/
theorem xiMin_eq_cKL_iff {μ : Fin 2 → Fin 2 → ℝ} (hμ : ∀ x y, 0 ≤ μ x y)
    (hμ1 : ∑ x, ∑ y, μ x y = 1) : xiMin μ = ENNReal.ofReal cKL ↔ ∀ x y, μ x y = 1 / 4 := by
  constructor
  · intro h
    by_contra hne
    exact (xiMin_lt_cKL hμ hμ1 hne).ne h
  · intro h
    refine le_antisymm (xiMin_le_cKL hμ hμ1) (le_xiMin (fun s hs h3 => ?_))
    simp only [h]
    exact cKL_le_obj_uniform hs h3

/-! ### The closed form (F.9) -/

/-- `λ ↦ Σ_e min{1, μ_e/λ}` is strictly decreasing below the value `4`. -/
theorem sum_min_lt {μ : Fin 2 → Fin 2 → ℝ} (hμ : ∀ x y, 0 < μ x y) {l₁ l₂ : ℝ} (h₁ : 0 < l₁)
    (h12 : l₁ < l₂) (hg : ∑ x, ∑ y, min 1 (μ x y / l₁) = 3) :
    ∑ x, ∑ y, min 1 (μ x y / l₂) < 3 := by
  have hex : ∃ x y, μ x y < l₁ := by
    by_contra hcon
    push_neg at hcon
    have h1 : ∀ x y, min 1 (μ x y / l₁) = 1 := fun x y =>
      min_eq_left ((one_le_div h₁).mpr (hcon x y))
    simp only [h1] at hg
    norm_num at hg
  obtain ⟨x0, y0, h0⟩ := hex
  have hle : ∀ x y, min 1 (μ x y / l₂) ≤ min 1 (μ x y / l₁) := fun x y =>
    min_le_min le_rfl (div_le_div_of_nonneg_left (hμ x y).le h₁ h12.le)
  have hlt : min 1 (μ x0 y0 / l₂) < min 1 (μ x0 y0 / l₁) := by
    rw [min_eq_right ((div_le_one h₁).mpr h0.le)]
    exact (min_le_right _ _).trans_lt (div_lt_div_of_pos_left (hμ x0 y0) h₁ h12)
  rw [← hg]
  exact Finset.sum_lt_sum (fun x _ => Finset.sum_le_sum (fun y _ => hle x y))
    ⟨x0, Finset.mem_univ _, Finset.sum_lt_sum (fun y _ => hle x0 y) ⟨y0, Finset.mem_univ _, hlt⟩⟩

/-- Theorem F.2: for a full-support input law there is a unique `λ > 0` with
`Σ_e min{1, μ_e/λ} = 3` (intermediate value theorem and strict monotonicity). -/
theorem exists_unique_xiLam {μ : Fin 2 → Fin 2 → ℝ} (hμ : ∀ x y, 0 < μ x y)
    (hμ1 : ∑ x, ∑ y, μ x y = 1) :
    ∃! lam : ℝ, 0 < lam ∧ ∑ x, ∑ y, min 1 (μ x y / lam) = 3 := by
  have hμle : ∀ x y, μ x y ≤ 1 := by
    intro x y
    have h1 : μ x y ≤ ∑ y', μ x y' :=
      Finset.single_le_sum (f := fun y' => μ x y') (fun y' _ => (hμ x y').le) (Finset.mem_univ y)
    have h2 : ∑ y', μ x y' ≤ ∑ x', ∑ y', μ x' y' :=
      Finset.single_le_sum (f := fun x' => ∑ y', μ x' y')
        (fun x' _ => Finset.sum_nonneg (fun y' _ => (hμ x' y').le)) (Finset.mem_univ x)
    linarith
  obtain ⟨m, hm_pos, hm_le⟩ : ∃ m : ℝ, 0 < m ∧ ∀ x y, m ≤ μ x y :=
    ⟨min (min (μ 0 0) (μ 0 1)) (min (μ 1 0) (μ 1 1)),
      lt_min (lt_min (hμ 0 0) (hμ 0 1)) (lt_min (hμ 1 0) (hμ 1 1)),
      Fin.forall_fin_two.mpr ⟨Fin.forall_fin_two.mpr ⟨(min_le_left _ _).trans (min_le_left _ _),
          (min_le_left _ _).trans (min_le_right _ _)⟩,
        Fin.forall_fin_two.mpr ⟨(min_le_right _ _).trans (min_le_left _ _),
          (min_le_right _ _).trans (min_le_right _ _)⟩⟩⟩
  have hm1 : m ≤ 1 := (hm_le 0 0).trans (hμle 0 0)
  have hcont : ContinuousOn (fun lam : ℝ => ∑ x, ∑ y, min 1 (μ x y / lam)) (Set.Icc m 1) := by
    refine continuousOn_finsetSum _ (fun x _ => continuousOn_finsetSum _ (fun y _ => ?_))
    exact (continuous_const.min continuous_id).comp_continuousOn
      (continuousOn_const.div continuousOn_id (fun lam hlam => (hm_pos.trans_le hlam.1).ne'))
  have hgm : ∑ x, ∑ y, min 1 (μ x y / m) = 4 := by
    have h1 : ∀ x y, min 1 (μ x y / m) = 1 := fun x y =>
      min_eq_left ((one_le_div hm_pos).mpr (hm_le x y))
    simp only [h1]
    norm_num
  have hg1 : ∑ x, ∑ y, min 1 (μ x y / 1) = 1 := by
    have h1 : ∀ x y, min 1 (μ x y / 1) = μ x y := fun x y => by
      rw [div_one, min_eq_right (hμle x y)]
    simp only [h1]
    exact hμ1
  obtain ⟨lam, hlam, hglam⟩ := intermediate_value_Icc' hm1 hcont
    (show (3 : ℝ) ∈ Set.Icc (∑ x, ∑ y, min 1 (μ x y / 1)) (∑ x, ∑ y, min 1 (μ x y / m)) by
      rw [hg1, hgm]
      norm_num [Set.mem_Icc])
  have hlam0 : 0 < lam := hm_pos.trans_le hlam.1
  refine ⟨lam, ⟨hlam0, hglam⟩, ?_⟩
  rintro lam' ⟨hlam'0, hglam'⟩
  rcases lt_trichotomy lam' lam with h | h | h
  · exact absurd hglam (sum_min_lt hμ hlam'0 h hglam').ne
  · exact h
  · exact absurd hglam' (sum_min_lt hμ hlam0 h hglam).ne

/-- Theorem F.2, (F.9): if `λ > 0` solves `Σ_e min{1, μ_e/λ} = 3` for a full-support input law,
then `Ξ(μ) = Σ_{μ_e < λ} μ_e log₂(λ/μ_e)`, attained at `s_e = min{1, μ_e/λ}`. -/
theorem xiMin_closed_form {μ : Fin 2 → Fin 2 → ℝ} (hμ : ∀ x y, 0 < μ x y) {lam : ℝ}
    (hlam : 0 < lam) (hg : ∑ x, ∑ y, min 1 (μ x y / lam) = 3) :
    xiMin μ = ENNReal.ofReal
      (∑ x, ∑ y, if μ x y < lam then μ x y * Real.logb 2 (lam / μ x y) else 0) := by
  have hspos : ∀ x y, 0 < min 1 (μ x y / lam) ∧ min 1 (μ x y / lam) ≤ 1 := fun x y =>
    ⟨lt_min one_pos (div_pos (hμ x y) hlam), min_le_left _ _⟩
  have hval : ∀ x y, μ x y * -Real.logb 2 (min 1 (μ x y / lam))
      = if μ x y < lam then μ x y * Real.logb 2 (lam / μ x y) else 0 := by
    intro x y
    by_cases h : μ x y < lam
    · rw [if_pos h, min_eq_right ((div_le_one hlam).mpr h.le), ← Real.logb_inv, inv_div]
    · rw [if_neg h, min_eq_left ((one_le_div hlam).mpr (not_lt.mp h)), Real.logb_one, neg_zero,
        mul_zero]
  have hobj : ∑ x, ∑ y, ENNReal.ofReal (μ x y) * negLogTwo (min 1 (μ x y / lam))
      = ENNReal.ofReal
        (∑ x, ∑ y, if μ x y < lam then μ x y * Real.logb 2 (lam / μ x y) else 0) := by
    rw [obj_eq_ofReal (s := fun x y => min 1 (μ x y / lam)) (fun x y => (hμ x y).le) hspos]
    simp only [hval]
  rw [← hobj]
  refine le_antisymm (xiMin_le (s := fun x y => min 1 (μ x y / lam))
    (fun x y => ⟨(hspos x y).1.le, (hspos x y).2⟩) hg) (le_xiMin (fun s hs h3 => ?_))
  by_cases hz : ∃ x y, s x y = 0
  · obtain ⟨x, y, hxy⟩ := hz
    rw [obj_eq_top (hμ x y) hxy]
    exact le_top
  push_neg at hz
  have hpos : ∀ x y, 0 < s x y ∧ s x y ≤ 1 := fun x y =>
    ⟨lt_of_le_of_ne (hs x y).1 (Ne.symm (hz x y)), (hs x y).2⟩
  rw [obj_eq_ofReal (s := fun x y => min 1 (μ x y / lam)) (fun x y => (hμ x y).le) hspos,
    obj_eq_ofReal (fun x y => (hμ x y).le) hpos]
  apply ENNReal.ofReal_le_ofReal
  rw [sum_mul_neg_logb, sum_mul_neg_logb]
  refine div_le_div_of_nonneg_right ?_ (Real.log_pos (by norm_num)).le
  have key : ∀ x y, μ x y * -Real.log (min 1 (μ x y / lam))
      ≤ μ x y * -Real.log (s x y) + lam * (s x y - min 1 (μ x y / lam)) := by
    intro x y
    have hs0 := (hpos x y).1
    by_cases h : μ x y < lam
    · have e : min 1 (μ x y / lam) = μ x y / lam := min_eq_right ((div_le_one hlam).mpr h.le)
      rw [e]
      have hst : 0 < μ x y / lam := div_pos (hμ x y) hlam
      have h1 := Real.log_le_sub_one_of_pos (div_pos hs0 hst)
      rw [Real.log_div hs0.ne' hst.ne'] at h1
      have h2 := mul_le_mul_of_nonneg_left h1 (hμ x y).le
      have e2 : μ x y * (s x y / (μ x y / lam) - 1) = lam * (s x y - μ x y / lam) := by
        rw [div_div_eq_mul_div, mul_sub, mul_sub, mul_one, mul_div_assoc',
          mul_div_cancel_left₀ _ (hμ x y).ne', mul_div_assoc', mul_div_cancel_left₀ _ hlam.ne']
        ring
      rw [e2, mul_sub] at h2
      rw [mul_neg, mul_neg]
      linarith
    · have e : min 1 (μ x y / lam) = 1 := min_eq_left ((one_le_div hlam).mpr (not_lt.mp h))
      rw [e, Real.log_one, neg_zero, mul_zero]
      have h1 := Real.log_le_sub_one_of_pos hs0
      have h3 := mul_le_mul_of_nonneg_left h1 (hμ x y).le
      have h4 : μ x y * (s x y - 1) ≤ lam * (s x y - 1) := by
        nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (not_lt.mp h))
          (sub_nonpos.mpr (hpos x y).2)]
      rw [mul_neg]
      linarith
  have hsum : ∑ x, ∑ y, μ x y * -Real.log (min 1 (μ x y / lam))
      ≤ ∑ x, ∑ y, (μ x y * -Real.log (s x y) + lam * (s x y - min 1 (μ x y / lam))) :=
    Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun y _ => key x y))
  have hzero : ∑ x, ∑ y, lam * (s x y - min 1 (μ x y / lam)) = 0 := by
    simp only [← Finset.mul_sum, Finset.sum_sub_distrib, h3, hg, sub_self, mul_zero]
  simp only [Finset.sum_add_distrib, hzero, add_zero] at hsum
  exact hsum

/-- **Theorem F.2, (F.9).** -/
theorem xi_closed_form_spec {μ : Fin 2 → Fin 2 → ℝ} (hμ : ∀ x y, 0 < μ x y)
    (hμ1 : ∑ x, ∑ y, μ x y = 1) :
    (∃! lam : ℝ, 0 < lam ∧ ∑ x, ∑ y, min 1 (μ x y / lam) = 3) ∧
      ∀ lam : ℝ, 0 < lam → ∑ x, ∑ y, min 1 (μ x y / lam) = 3 →
        xiMin μ = ENNReal.ofReal
          (∑ x, ∑ y, if μ x y < lam then μ x y * Real.logb 2 (lam / μ x y) else 0) :=
  ⟨exists_unique_xiLam hμ hμ1, fun _ hlam hg => xiMin_closed_form hμ hlam hg⟩

end

end CGLMPBounds
