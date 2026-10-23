module

public import CGLMPBounds.BGP.FacetRank

@[expose] public section


/-!
# Proposition G.1: Table G.1, the relative-interior point `p̄` and the rational point `p⁺`

Supplement, Appendix G (proof of Proposition G.1):
* "Evaluation on the `4⁴` strategies gives Table G.1": values `0, −1, −2` on `72, 144, 40`
  strategies;
* "The average `p̄ = (1/72) Σ_{s∈S} q_s` has minimum entry `1/72` … Since probability nonnegativity
  defines `P₄` in its affine hull, `p̄` is a relative-interior point";
* "Modify only context `00`, adding `1/144` at `(0, 1)`, `(3, 3)` and subtracting `1/144` at
  `(0, 3)`, `(3, 1)`. The resulting `p⁺` preserves all row and column sums, remains nonnegative, and
  satisfies `F(p⁺) = 1/144`."

The relative interior is Mathlib's `intrinsicInterior`. A point `z` of the affine span of `P₄` differs
from `p̄` by a normalized no-signalling direction (`vectorSpan_noSignalling_le`). When
`‖z - p̄‖ < 1/72`, all entries of `z` are positive, so `z ∈ P₄`.

* `bgp_local_valid_spec`, `bgp_deterministic_values_spec`, `bgp_relative_interior_point_spec`,
  `bgp_no_signalling_violation_spec` : the forms of the Challenge endpoints.
-/

namespace CGLMPBounds

open Finset

/-! ### Integer tables -/

/-- `F` on an integer table. -/
def bgpValZ (t : Fin 2 → Fin 2 → Fin 4 → Fin 4 → ℤ) : ℤ :=
  (∑ x : Fin 2, ∑ a : Fin 3, bgpL (bgpIndex x a) * ∑ b, t x 0 a.castSucc b)
    + (∑ y : Fin 2, ∑ b : Fin 3, bgpL (bgpIndex y b) * ∑ a, t 0 y a b.castSucc)
    + ∑ x : Fin 2, ∑ y : Fin 2, ∑ a : Fin 3, ∑ b : Fin 3,
        bgpH (bgpIndex x a) (bgpIndex y b) * t x y a.castSucc b.castSucc

theorem bgpFunctional_intCast (t : Fin 2 → Fin 2 → Fin 4 → Fin 4 → ℤ) :
    bgpFunctional (fun x y a b => (t x y a b : ℝ)) = (bgpValZ t : ℝ) := by
  unfold bgpFunctional bgpValZ
  push_cast
  try rfl

/-! ### Table G.1 -/

theorem bgpDetVal_cases_mk : ∀ a₀ a₁ b₀ b₁ : Fin 4,
    bgpDetVal (![a₀, a₁], ![b₀, b₁]) = 0 ∨ bgpDetVal (![a₀, a₁], ![b₀, b₁]) = -1 ∨
      bgpDetVal (![a₀, a₁], ![b₀, b₁]) = -2 := by
  decide +kernel

theorem bgpFunctional_detTable_eq_iff (s : Strategy (Fin 4) (Fin 4)) (c : ℤ) :
    bgpFunctional (detTable s) = (c : ℝ) ↔ bgpDetVal s = c := by
  rw [bgpFunctional_detTable]
  exact Int.cast_inj

theorem bgp_card_zero :
    (Finset.univ.filter (fun s : Strategy (Fin 4) (Fin 4) => bgpDetVal s = 0)).card = 72 := by
  decide +kernel

theorem bgp_card_neg_one :
    (Finset.univ.filter (fun s : Strategy (Fin 4) (Fin 4) => bgpDetVal s = -1)).card = 144 := by
  decide +kernel

theorem bgp_card_neg_two :
    (Finset.univ.filter (fun s : Strategy (Fin 4) (Fin 4) => bgpDetVal s = -2)).card = 40 := by
  decide +kernel

/-- **Table G.1**, in the form of the Challenge endpoint. -/
theorem bgp_deterministic_values_spec :
    (∀ s : Strategy (Fin 4) (Fin 4),
      bgpFunctional (detTable s) = 0 ∨ bgpFunctional (detTable s) = -1 ∨
        bgpFunctional (detTable s) = -2) ∧
      (Finset.univ.filter (fun s : Strategy (Fin 4) (Fin 4) =>
        bgpFunctional (detTable s) = 0)).card = 72 ∧
      (Finset.univ.filter (fun s : Strategy (Fin 4) (Fin 4) =>
        bgpFunctional (detTable s) = -1)).card = 144 ∧
      (Finset.univ.filter (fun s : Strategy (Fin 4) (Fin 4) =>
        bgpFunctional (detTable s) = -2)).card = 40 := by
  have h0 : ∀ s : Strategy (Fin 4) (Fin 4), bgpFunctional (detTable s) = 0 ↔ bgpDetVal s = 0 :=
    fun s => by simpa using bgpFunctional_detTable_eq_iff s 0
  have h1 : ∀ s : Strategy (Fin 4) (Fin 4), bgpFunctional (detTable s) = -1 ↔ bgpDetVal s = -1 :=
    fun s => by simpa using bgpFunctional_detTable_eq_iff s (-1)
  have h2 : ∀ s : Strategy (Fin 4) (Fin 4), bgpFunctional (detTable s) = -2 ↔ bgpDetVal s = -2 :=
    fun s => by simpa using bgpFunctional_detTable_eq_iff s (-2)
  refine ⟨fun s => ?_, ?_, ?_, ?_⟩
  · rw [h0, h1, h2, strategy_eq_mk s]
    exact bgpDetVal_cases_mk (s.1 0) (s.1 1) (s.2 0) (s.2 1)
  · rw [Finset.filter_congr (fun s _ => h0 s)]
    exact bgp_card_zero
  · rw [Finset.filter_congr (fun s _ => h1 s)]
    exact bgp_card_neg_one
  · rw [Finset.filter_congr (fun s _ => h2 s)]
    exact bgp_card_neg_two

/-- **Local validity**, in the form of the Challenge endpoint. -/
theorem bgp_local_valid_spec (q : Table (Fin 4) (Fin 4)) (hq : q ∈ localSet (Fin 4) (Fin 4)) :
    bgpFunctional q ≤ 0 :=
  bgpFunctional_nonpos_of_mem_localSet hq

/-! ### The saturator average `p̄` -/

/-- The number of saturators with outcomes `(a, b)` in the context `(x, y)`. -/
def bgpSatCount (x y : Fin 2) (a b : Fin 4) : ℕ :=
  ((Finset.univ.filter (fun s : Strategy (Fin 4) (Fin 4) => bgpDetVal s = 0)).filter
    (fun s => a = s.1 x ∧ b = s.2 y)).card

theorem bgpSatCount_pos : ∀ x y : Fin 2, ∀ a b : Fin 4, 1 ≤ bgpSatCount x y a b := by
  decide +kernel

theorem bgpSatCount_zero : bgpSatCount 0 0 0 0 = 1 := by
  decide +kernel

/-- `p̄ = (1/72) Σ_{s ∈ S} q_s` entrywise: `p̄(a,b|x,y) = #{s ∈ S : a_x = a, b_y = b}/72`. -/
theorem bgp_pbar_apply (x y : Fin 2) (a b : Fin 4) :
    ((1 / 72 : ℝ) • ∑ s ∈ Finset.univ.filter (fun s : Strategy (Fin 4) (Fin 4) =>
        bgpFunctional (detTable s) = 0), detTable s) x y a b = (bgpSatCount x y a b : ℝ) / 72 := by
  have hS : Finset.univ.filter (fun s : Strategy (Fin 4) (Fin 4) => bgpFunctional (detTable s) = 0)
      = Finset.univ.filter (fun s : Strategy (Fin 4) (Fin 4) => bgpDetVal s = 0) :=
    Finset.filter_congr (fun s _ => by simpa using bgpFunctional_detTable_eq_iff s 0)
  rw [hS]
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, detTable]
  rw [Finset.sum_boole]
  unfold bgpSatCount
  ring

/-- The normalized no-signalling tables span at most the no-signalling directions. -/
theorem vectorSpan_noSignalling_le :
    vectorSpan ℝ {q : Table (Fin 4) (Fin 4) | IsNoSignalling q} ≤ bgpNSDirection := by
  rw [vectorSpan_def, Submodule.span_le]
  rintro _ ⟨p, hp, q, hq, rfl⟩
  exact sub_mem_bgpNSDirection hp hq

/-- A table within sup-distance `δ` of a table with all entries `≥ δ`, differing from it by a
no-signalling direction, is a no-signalling behaviour. -/
theorem isNoSignalling_of_near {p z : Table (Fin 4) (Fin 4)} (hp : IsNoSignalling p) {δ : ℝ}
    (hpδ : ∀ x y a b, δ ≤ p x y a b) (hdir : z - p ∈ bgpNSDirection) (hz : ‖z - p‖ < δ) :
    IsNoSignalling z := by
  obtain ⟨hw1, hw2, hw3⟩ := hdir
  have hentry : ∀ x y a b, |(z - p) x y a b| < δ := by
    intro x y a b
    calc |(z - p) x y a b| = ‖(z - p) x y a b‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖(z - p) x y a‖ := norm_le_pi_norm ((z - p) x y a) b
      _ ≤ ‖(z - p) x y‖ := norm_le_pi_norm ((z - p) x y) a
      _ ≤ ‖(z - p) x‖ := norm_le_pi_norm ((z - p) x) y
      _ ≤ ‖z - p‖ := norm_le_pi_norm (z - p) x
      _ < δ := hz
  have hz_eq : ∀ x y a b, z x y a b = p x y a b + (z - p) x y a b := by
    intro x y a b
    simp only [Pi.sub_apply]
    ring
  refine ⟨⟨fun x y a b => ?_, fun x y => ?_⟩, fun x y y' a => ?_, fun x x' y b => ?_⟩
  · have h1 := hentry x y a b
    have h2 := hpδ x y a b
    rw [hz_eq x y a b]
    have := neg_abs_le ((z - p) x y a b)
    linarith
  · have h := hw1 x y
    simp only [Pi.sub_apply, Finset.sum_sub_distrib, hp.isBehaviour.sum_eq_one] at h
    linarith
  · have h := hw2 x y y' a
    simp only [Pi.sub_apply, Finset.sum_sub_distrib, hp.margA_indep x y y' a] at h
    linarith
  · have h := hw3 x x' y b
    simp only [Pi.sub_apply, Finset.sum_sub_distrib, hp.margB_indep x x' y b] at h
    linarith

set_option maxHeartbeats 1000000 in
/-- **The relative-interior point**, in the form of the Challenge endpoint. -/
theorem bgp_relative_interior_point_spec (pbar : Table (Fin 4) (Fin 4))
    (hpbar : pbar = (1 / 72 : ℝ) • ∑ s ∈ Finset.univ.filter
      (fun s : Strategy (Fin 4) (Fin 4) => bgpFunctional (detTable s) = 0), detTable s) :
    pbar ∈ localSet (Fin 4) (Fin 4) ∧ bgpFunctional pbar = 0 ∧
      IsNoSignalling pbar ∧ (∀ x y a b, 1 / 72 ≤ pbar x y a b) ∧
      (∃ x y a b, pbar x y a b = 1 / 72) ∧
      pbar ∈ intrinsicInterior ℝ {q : Table (Fin 4) (Fin 4) | IsNoSignalling q} := by
  set S := Finset.univ.filter
    (fun s : Strategy (Fin 4) (Fin 4) => bgpFunctional (detTable s) = 0) with hSdef
  have hcard : S.card = 72 := bgp_deterministic_values_spec.2.1
  have hentry : ∀ x y a b, pbar x y a b = (bgpSatCount x y a b : ℝ) / 72 := by
    intro x y a b
    rw [hpbar]
    exact bgp_pbar_apply x y a b
  -- `p̄` is local
  have hloc : pbar ∈ localSet (Fin 4) (Fin 4) := by
    rw [hpbar, Finset.smul_sum]
    refine (convex_convexHull ℝ _).sum_mem (fun _ _ => by norm_num) ?_
      (fun s _ => subset_convexHull ℝ _ ⟨s, rfl⟩)
    rw [Finset.sum_const, hcard, nsmul_eq_mul]
    norm_num
  have hNS := isNoSignalling_of_mem_localSet hloc
  -- `F(p̄) = 0`
  have hF : bgpFunctional pbar = 0 := by
    rw [← bgpLin_apply, hpbar, map_smul, map_sum]
    have : ∀ s ∈ S, bgpLin (detTable s) = 0 := by
      intro s hs
      rw [bgpLin_apply]
      exact (Finset.mem_filter.mp hs).2
    rw [Finset.sum_eq_zero this, smul_zero]
  -- the entries
  have hge : ∀ x y a b, 1 / 72 ≤ pbar x y a b := by
    intro x y a b
    rw [hentry]
    have : (1 : ℝ) ≤ bgpSatCount x y a b := by exact_mod_cast bgpSatCount_pos x y a b
    linarith
  have hmin : ∃ x y a b, pbar x y a b = 1 / 72 :=
    ⟨0, 0, 0, 0, by rw [hentry, bgpSatCount_zero]; norm_num⟩
  refine ⟨hloc, hF, hNS, hge, hmin, ?_⟩
  -- the relative interior
  rw [mem_intrinsicInterior]
  refine ⟨⟨pbar, subset_affineSpan ℝ _ hNS⟩, ?_, rfl⟩
  rw [mem_interior_iff_mem_nhds, mem_nhds_subtype]
  refine ⟨Metric.ball pbar (1 / 72), Metric.ball_mem_nhds _ (by norm_num), ?_⟩
  rintro ⟨z, hz⟩ hzball
  show IsNoSignalling z
  have hdir : z - pbar ∈ bgpNSDirection := by
    have h1 : z -ᵥ pbar ∈
        (affineSpan ℝ {q : Table (Fin 4) (Fin 4) | IsNoSignalling q}).direction :=
      AffineSubspace.vsub_mem_direction hz (subset_affineSpan ℝ _ hNS)
    rw [direction_affineSpan] at h1
    exact vectorSpan_noSignalling_le h1
  have hdist : ‖z - pbar‖ < 1 / 72 := by
    have h : dist z pbar < (1 / 72 : ℝ) := hzball
    rwa [dist_eq_norm] at h
  exact isNoSignalling_of_near hNS hge hdir hdist

/-! ### The rational no-signalling point `p⁺` -/

/-- The perturbation of context `00`: `+1` at `(0, 1)` and `(3, 3)`, `-1` at `(0, 3)` and `(3, 1)`. -/
def bgpPerturb (x y : Fin 2) (a b : Fin 4) : ℤ :=
  if x = 0 ∧ y = 0 then
    (if (a = 0 ∧ b = 1) ∨ (a = 3 ∧ b = 3) then 1
      else if (a = 0 ∧ b = 3) ∨ (a = 3 ∧ b = 1) then -1 else 0)
  else 0

theorem bgpValZ_perturb : bgpValZ bgpPerturb = 1 := by
  decide +kernel

theorem bgpPerturb_rows : ∀ x y : Fin 2, ∀ a : Fin 4, ∑ b, bgpPerturb x y a b = 0 := by
  decide +kernel

theorem bgpPerturb_cols : ∀ x y : Fin 2, ∀ b : Fin 4, ∑ a, bgpPerturb x y a b = 0 := by
  decide +kernel

theorem bgpPerturb_abs : ∀ x y : Fin 2, ∀ a b : Fin 4,
    bgpPerturb x y a b = -1 ∨ bgpPerturb x y a b = 0 ∨ bgpPerturb x y a b = 1 := by
  decide +kernel

/-- **The rational no-signalling point `p⁺` with `F(p⁺) = 1/144`**, in the form of the Challenge
endpoint. -/
theorem bgp_no_signalling_violation_spec :
    ∃ p : Table (Fin 4) (Fin 4), IsNoSignalling p ∧
      (∀ x y a b, ∃ r : ℚ, p x y a b = r) ∧ bgpFunctional p = 1 / 144 := by
  set pbar : Table (Fin 4) (Fin 4) := (1 / 72 : ℝ) • ∑ s ∈ Finset.univ.filter
    (fun s : Strategy (Fin 4) (Fin 4) => bgpFunctional (detTable s) = 0), detTable s with hpbar
  obtain ⟨-, hF, hNS, hge, -, -⟩ := bgp_relative_interior_point_spec pbar hpbar
  set δ : Table (Fin 4) (Fin 4) := fun x y a b => ((bgpPerturb x y a b : ℤ) : ℝ) with hδ
  refine ⟨pbar + (1 / 144 : ℝ) • δ, ?_, fun x y a b => ?_, ?_⟩
  · -- no-signalling: `δ` is a normalized no-signalling direction, and `p̄ ≥ 1/72 > 1/144 ≥ |δ|/144`
    have hrow : ∀ x y a, ∑ b, δ x y a b = 0 := by
      intro x y a
      simp only [hδ]
      exact_mod_cast bgpPerturb_rows x y a
    have hcol : ∀ x y b, ∑ a, δ x y a b = 0 := by
      intro x y b
      simp only [hδ]
      exact_mod_cast bgpPerturb_cols x y b
    refine ⟨⟨fun x y a b => ?_, fun x y => ?_⟩, fun x y y' a => ?_, fun x x' y b => ?_⟩
    · have h1 := hge x y a b
      have h2 : -1 ≤ δ x y a b := by
        simp only [hδ]
        rcases bgpPerturb_abs x y a b with h | h | h <;> rw [h] <;> norm_num
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linarith
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
        ← Finset.mul_sum, hrow, hNS.isBehaviour.sum_eq_one]
      simp
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
        ← Finset.mul_sum, hrow, hNS.margA_indep x y y' a]
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
        ← Finset.mul_sum, hcol, hNS.margB_indep x x' y b]
  · -- rational entries
    refine ⟨(bgpSatCount x y a b : ℚ) / 72 + (1 / 144 : ℚ) * (bgpPerturb x y a b : ℚ), ?_⟩
    have h := bgp_pbar_apply x y a b
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hδ]
    rw [show pbar x y a b = (bgpSatCount x y a b : ℝ) / 72 from h]
    first
      | (push_cast; ring)
      | push_cast
  · -- `F(p⁺) = F(p̄) + F(δ)/144 = 1/144`
    have hFδ : bgpFunctional δ = 1 := by
      rw [hδ, bgpFunctional_intCast, bgpValZ_perturb, Int.cast_one]
    change bgpLin (pbar + (1 / 144 : ℝ) • δ) = 1 / 144
    rw [map_add, bgpLin.map_smul (1 / 144 : ℝ) δ,
      bgpLin_apply pbar, bgpLin_apply δ, hF, hFδ]
    norm_num

end CGLMPBounds
