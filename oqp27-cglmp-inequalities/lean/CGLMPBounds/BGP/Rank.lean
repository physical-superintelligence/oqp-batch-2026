module

public import CGLMPBounds.Defs.BGPRank
public import CGLMPBounds.Defs.BGP
public import CGLMPBounds.Scenario.Local
public import CGLMPBounds.Statistics.Gluing

@[expose] public section


/-!
# Proposition G.1: the rank certificate (G.2)

Supplement, proof of Proposition G.1: "Let `S = {s : F(s) = 0}`, and augment the coordinates
`z(s) = (1, A(s), B(s), (A_i(s) B_j(s))_{i,j=0}^5)`, `ι(s) = 64a₀ + 16a₁ + 4b₀ + b₁`, with the
products in row-major order. Select the rows with the ordered identifiers in Table G.2. Numbering
columns from zero and deleting column 47 gives a 48 × 48 matrix `Z_min` with `det Z_min = −1`
(G.2). Thus the saturation face has affine rank 47." The coordinates are `A(s) = (1{a₀=0},
1{a₀=1}, 1{a₀=2}, 1{a₁=0}, 1{a₁=1}, 1{a₁=2})` and `B(s)` likewise.

Here `Z_min` is `bgpRankZ`. Its inverse is the integer matrix with the sparse columns `bgpRankW`,
and `bgpRank_cert` checks `Z_min W = I` by `decide`. The determinant is not needed: invertibility
of `Z_min` already gives the affine independence of the 48 rows of Table G.2.

* `bgp_rank_saturators_affineIndependent` : the deterministic tables of Table G.2 are affinely
  independent;
* `bgpNSDirection`, `finrank_bgpNSDirection_le` : the direction space of the normalized
  no-signalling tables (the source's "affine dimension is 48") has dimension at most 48;
* `vectorSpan_localSet_le` : the local polytope `C₄` spans at most these directions.
-/

namespace CGLMPBounds

open Finset

/-! ### Table G.2 and the augmented coordinates -/

def bgpRankW : Fin 48 → List (Fin 48 × ℤ) :=
  ![
    [(0, -1), (2, 1), (3, 1), (4, 1), (5, 1), (7, -1), (10, 1), (11, 1), (12, 2), (13, 1),
      (18, -1), (19, 1), (22, -1), (23, -1), (24, -2), (25, 1), (26, -1), (28, -1), (30, -2),
      (32, 1), (34, -1), (35, -1), (36, -2), (40, -1), (41, -1), (42, -1)],
    [(7, 1), (12, -1), (13, -1), (18, 1), (19, -1), (24, 1), (25, -1), (30, 1), (36, 1)],
    [(1, 1), (7, 1), (8, 1), (12, -1), (13, -1), (14, -1), (19, -1), (24, 1), (25, -1), (30, 1),
      (32, -1), (36, 1), (38, -1), (42, 1)],
    [(0, 1), (1, -1), (2, -1), (3, -1), (4, -1), (5, -1), (8, -1), (10, -1), (11, -1), (12, -1),
      (14, 1), (16, 1), (18, 1), (22, 1), (23, 1), (24, 1), (26, 1), (28, 1), (30, 1), (34, 1),
      (35, 1), (36, 1), (38, 1), (40, 1), (41, 1)],
    [(17, 1)],
    [(42, 1)],
    [(1, 1), (16, -1), (17, -1), (18, -1)],
    [(13, 1)],
    [(44, 1)],
    [(45, 1)],
    [(7, -1), (19, 1), (24, -1), (25, 1), (30, -1), (44, -1), (45, -1), (47, 1)],
    [(8, 1), (32, -1), (38, -1), (44, -1)],
    [(1, -1), (7, -1), (8, -1), (12, 1), (13, 1), (14, 1), (15, 1), (19, 1), (24, -1), (25, 1),
      (30, -1), (32, 1), (36, -1), (38, 1), (42, -1), (45, -1)],
    [(1, 1), (7, 1), (13, -1), (14, -1), (15, -1), (19, -1), (24, 1), (25, -1), (30, 1), (44, 1),
      (45, 1), (47, -1)],
    [(1, 1), (6, 1), (7, 2), (8, 1), (9, 1), (12, -1), (13, -1), (14, -1), (15, -1), (19, -2),
      (21, -1), (22, 1), (24, 2), (25, -2), (30, 2), (32, -1), (33, -1), (36, 1), (38, -1),
      (42, 1), (43, -1), (46, -1), (47, -1)],
    [(4, 1), (7, -1), (9, -1), (10, 1), (12, 1), (13, 1), (15, 1), (16, -1), (18, -1), (19, 1),
      (21, 1), (22, -1), (24, -1), (25, 1), (27, 1), (28, -1), (30, -1), (34, -1), (36, -1)],
    [(1, -1), (7, -1), (8, -1), (9, -1), (12, 1), (13, 1), (14, 1), (15, 1), (19, 1), (21, 1),
      (24, -1), (25, 1), (30, -1), (32, 1), (33, 1), (36, -1), (38, 1), (42, -1)],
    [(37, 1)],
    [(20, 1)],
    [(39, 1)],
    [(4, -1), (7, 1), (9, 1), (10, -1), (11, -1), (12, -1), (13, -1), (15, -1), (16, 1), (18, 1),
      (19, -1), (20, -1), (21, -1), (22, 1), (23, 1), (24, 1), (25, -1), (27, -1), (28, 1),
      (30, 1), (34, 1), (35, 1), (36, 1), (37, -1), (39, -1), (41, 1)],
    [(6, -1), (7, -1), (19, 1), (24, -1), (25, 1), (30, -1), (43, 1), (46, 1), (47, 1)],
    [(1, -1), (2, -1), (4, -1), (7, -1), (8, -1), (10, -1), (14, 1), (16, 1), (18, 1), (19, 1),
      (22, 1), (23, 1), (27, -1), (28, 1), (31, 1), (32, 1), (33, 1), (34, 1), (38, 1), (42, -1),
      (43, 1)],
    [(24, 1)],
    [(2, 1), (22, -1), (23, -1), (24, -1)],
    [(7, 1), (31, -1), (37, -1), (43, -1)],
    [(1, 1), (7, 1), (8, 1), (9, 1), (12, -1), (13, -1), (14, -1), (15, -1), (19, -1), (24, 1),
      (25, -1), (30, 1), (32, -1), (33, -1), (36, 1), (38, -1), (39, -1), (42, 1)],
    [(2, 1), (4, 1), (7, -1), (9, -1), (10, 1), (11, 1), (12, 1), (13, 1), (15, 1), (16, -1),
      (18, -1), (22, -1), (23, -1), (24, -1), (25, 1), (27, 1), (28, -1), (30, -1), (34, -1),
      (35, -1), (36, -1), (37, 1), (39, 1), (41, -1)],
    [(1, -1), (4, -1), (6, -1), (7, -1), (8, -1), (10, -1), (14, 1), (16, 1), (18, 1), (19, 1),
      (24, -1), (25, 1), (27, -1), (28, 1), (30, -1), (31, 1), (32, 1), (33, 1), (34, 1), (38, 1),
      (42, -1), (43, 1), (46, 1), (47, 1)],
    [(0, 1), (2, -1), (3, -1), (4, -1), (5, -1), (10, -1), (11, -1), (12, -1), (22, 1), (23, 1),
      (24, 1), (26, 1), (28, 1), (30, 1), (34, 1), (35, 1), (36, 1), (40, 1), (41, 1), (42, 1)],
    [(27, 1)],
    [(4, 1), (31, -1), (32, -1), (33, -1)],
    [(29, 1)],
    [(0, -1), (2, 1), (3, 1), (4, 1), (5, 1), (10, 1), (11, 1), (12, 1), (22, -1), (23, -1),
      (24, -1), (28, -1), (29, -1), (30, -1), (34, -1), (35, -1), (36, -1), (40, -1), (41, -1),
      (42, -1)],
    [(0, -1), (1, 1), (2, 1), (3, 1), (4, 1), (5, 1), (8, 1), (10, 1), (11, 1), (12, 1), (14, -1),
      (16, -1), (18, -1), (22, -1), (23, -1), (24, -1), (26, -1), (28, -1), (30, -1), (34, -1),
      (35, -1), (36, -1), (38, -1), (41, -1)],
    [(30, 1)],
    [(1, 1), (4, 1), (6, 1), (7, 1), (8, 1), (10, 1), (14, -1), (16, -1), (18, -1), (19, -1),
      (24, 1), (27, 1), (28, -1), (31, -1), (32, -1), (33, -1), (34, -1), (38, -1), (42, 1),
      (43, -1), (46, -1), (47, -1)],
    [(6, 1), (7, 1), (19, -1), (24, 1), (25, -1), (30, 1), (43, -1), (47, -1)],
    [(10, 1), (34, -1), (40, -1), (46, -1)],
    [(0, 1), (1, -1), (2, -1), (4, -2), (5, -1), (6, -1), (7, -1), (8, -1), (10, -2), (11, -1),
      (12, -1), (14, 1), (16, 1), (18, 1), (19, 1), (22, 1), (23, 1), (27, -1), (28, 1), (31, 1),
      (32, 1), (33, 1), (34, 2), (35, 1), (36, 1), (38, 1), (40, 1), (41, 1), (43, 1), (46, 1),
      (47, 1)],
    [(10, 1), (16, -1), (22, -1), (28, -1)],
    [(4, -1), (7, 1), (9, 1), (10, -1), (12, -1), (13, -1), (15, -1), (16, 1), (18, 1), (19, -1),
      (21, -1), (22, 1), (24, 1), (25, -1), (27, -1), (28, 1), (30, 1), (34, 1), (35, 1), (36, 1)],
    [(7, -1), (12, 1), (13, 1), (18, -1), (19, 1), (24, -1), (25, 1), (30, -1)],
    [(4, 1), (34, -1), (35, -1), (36, -1)],
    [(0, -1), (1, 1), (2, 1), (3, 1), (4, 1), (8, 1), (10, 1), (11, 1), (12, 1), (14, -1),
      (16, -1), (17, -1), (18, -1), (20, -1), (22, -1), (23, -1), (24, -1), (26, -1), (28, -1),
      (29, -1), (30, -1), (34, -1), (35, -1), (36, -1)],
    [(0, 1), (1, -1), (2, -1), (3, -1), (4, -1), (10, -1), (11, -1), (12, -1), (16, 1), (17, 1),
      (18, 1), (22, 1), (23, 1), (24, 1), (28, 1), (29, 1), (30, 1), (34, 1), (35, 1), (36, 1)],
    [(0, 1), (1, -1), (2, -1), (3, -1), (7, -1), (8, -1), (9, -1), (13, 1), (14, 1), (15, 1),
      (19, 1), (20, 1), (21, 1), (25, 1), (26, 1), (27, 1)],
    [(7, 1), (13, -1), (19, -1), (25, -1)]]

/-- **The certificate.** `Z_min W = I` for the integer matrix `W` with columns `bgpRankW`. -/
theorem bgpRank_cert : ∀ i j : Fin 48,
    ((bgpRankW j).map (fun p => p.2 * bgpRankZ i p.1)).sum = if i = j then 1 else 0 := by
  decide +kernel

/-! ### The coordinates as sums of table entries -/

/-- The table entries whose sum is `z_c` for `1 ≤ c ≤ 48`: Alice's marginal `Σ_b p(a,b|x,0)`, Bob's
marginal `Σ_a p(a,b|0,y)`, or one joint entry. -/
def bgpEntries (c : ℕ) : List (Fin 2 × Fin 2 × Fin 4 × Fin 4) :=
  if c ≤ 6 then
    [0, 1, 2, 3].map (fun b : Fin 4 =>
      ((if c - 1 < 3 then 0 else 1), 0, ⟨(c - 1) % 3, by omega⟩, b))
  else if c ≤ 12 then
    [0, 1, 2, 3].map (fun a : Fin 4 =>
      (0, (if c - 7 < 3 then 0 else 1), a, ⟨(c - 7) % 3, by omega⟩))
  else
    [((if (c - 13) / 6 < 3 then 0 else 1), (if (c - 13) % 6 < 3 then 0 else 1),
      ⟨(c - 13) / 6 % 3, by omega⟩, ⟨(c - 13) % 6 % 3, by omega⟩)]

/-- The entry `q_s(a,b|x,y) ∈ {0, 1}` of a deterministic table, as an integer. -/
def bgpEntryVal (s : Strategy (Fin 4) (Fin 4)) (e : Fin 2 × Fin 2 × Fin 4 × Fin 4) : ℤ :=
  if e.2.2.1 = s.1 e.1 ∧ e.2.2.2 = s.2 e.2.1 then 1 else 0

theorem bgpRankZ_zero : ∀ i : Fin 48, bgpRankZ i 0 = 1 := by
  decide +kernel

theorem bgpRankZ_eq_entries : ∀ i c : Fin 48, c ≠ 0 →
    bgpRankZ i c = ((bgpEntries (bgpRankCol c)).map (bgpEntryVal (bgpRankStrategy i))).sum := by
  decide +kernel

theorem detTable_eq_bgpEntryVal (s : Strategy (Fin 4) (Fin 4)) (x y : Fin 2) (a b : Fin 4) :
    detTable s x y a b = (bgpEntryVal s (x, y, a, b) : ℝ) := by
  unfold detTable bgpEntryVal
  by_cases h : a = s.1 x ∧ b = s.2 y <;> simp [h]

/-! ### List-sum bookkeeping -/

theorem cast_list_sum_map {E : Type*} (f : E → ℤ) (l : List E) :
    (((l.map f).sum : ℤ) : ℝ) = (l.map (fun e => (f e : ℝ))).sum := by
  induction l with
  | nil => simp
  | cons e l ih => simp [ih]

theorem sum_mul_list_sum {ι E : Type*} [Fintype ι] (w : ι → ℝ) (g : ι → E → ℝ) (l : List E) :
    ∑ i, w i * (l.map (g i)).sum = (l.map (fun e => ∑ i, w i * g i e)).sum := by
  induction l with
  | nil => simp
  | cons e l ih => simp only [List.map_cons, List.sum_cons, mul_add, Finset.sum_add_distrib, ih]

theorem list_sum_map_eq_zero {E : Type*} (f : E → ℝ) (l : List E) (h : ∀ e ∈ l, f e = 0) :
    (l.map f).sum = 0 := by
  induction l with
  | nil => simp
  | cons e l ih =>
    rw [List.map_cons, List.sum_cons, h e List.mem_cons_self,
      ih (fun e' he' => h e' (List.mem_cons_of_mem _ he')), add_zero]

/-! ### Affine independence of the saturators -/

/-- **(G.2).** The 48 deterministic tables of Table G.2 are affinely independent. -/
theorem bgp_rank_saturators_affineIndependent :
    AffineIndependent ℝ (fun i : Fin 48 => detTable (bgpRankStrategy i)) := by
  rw [affineIndependent_iff_of_fintype]
  intro w hw0 hwv
  rw [Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero _ _ _ hw0 0,
    Finset.weightedVSubOfPoint_apply] at hwv
  simp only [vsub_eq_sub, sub_zero] at hwv
  -- the vanishing combination, entry by entry
  have hent : ∀ e : Fin 2 × Fin 2 × Fin 4 × Fin 4,
      ∑ i, w i * (bgpEntryVal (bgpRankStrategy i) e : ℝ) = 0 := by
    rintro ⟨x, y, a, b⟩
    have h := congrFun (congrFun (congrFun (congrFun hwv x) y) a) b
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
    rw [← h]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [detTable_eq_bgpEntryVal]
  -- the vanishing combination of the rows of `Z_min`
  have hcol : ∀ c : Fin 48, ∑ i, w i * (bgpRankZ i c : ℝ) = 0 := by
    intro c
    by_cases hc : c = 0
    · subst hc
      simp only [bgpRankZ_zero, Int.cast_one, mul_one]
      exact hw0
    · have hz : ∀ i, (bgpRankZ i c : ℝ)
          = ((bgpEntries (bgpRankCol c)).map
              (fun e => (bgpEntryVal (bgpRankStrategy i) e : ℝ))).sum := by
        intro i
        rw [bgpRankZ_eq_entries i c hc, cast_list_sum_map]
      simp only [hz]
      rw [sum_mul_list_sum]
      exact list_sum_map_eq_zero _ _ (fun e _ => hent e)
  -- invert `Z_min`
  intro j
  have hdelta : w j = ∑ i, w i * (((if i = j then 1 else 0 : ℤ)) : ℝ) := by
    simp
  rw [hdelta]
  simp only [← bgpRank_cert]
  have hexp : ∀ i, (((bgpRankW j).map (fun p => p.2 * bgpRankZ i p.1)).sum : ℝ)
      = ((bgpRankW j).map (fun p => (p.2 : ℝ) * (bgpRankZ i p.1 : ℝ))).sum := by
    intro i
    rw [cast_list_sum_map]
    push_cast
    rfl
  simp only [hexp]
  rw [sum_mul_list_sum]
  refine list_sum_map_eq_zero _ _ (fun p _ => ?_)
  have h := hcol p.1
  calc ∑ i, w i * ((p.2 : ℝ) * (bgpRankZ i p.1 : ℝ))
      = (p.2 : ℝ) * ∑ i, w i * (bgpRankZ i p.1 : ℝ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        ring
    _ = 0 := by rw [h, mul_zero]

/-! ### The no-signalling directions have dimension at most 48 -/

/-- The direction space of the normalized no-signalling tables: zero context sums and
input-independent marginals. -/
def bgpNSDirection : Submodule ℝ (Table (Fin 4) (Fin 4)) where
  carrier := {v | (∀ x y, ∑ a, ∑ b, v x y a b = 0) ∧
    (∀ x y y' a, ∑ b, v x y a b = ∑ b, v x y' a b) ∧
    (∀ x x' y b, ∑ a, v x y a b = ∑ a, v x' y a b)}
  add_mem' := by
    rintro u v ⟨hu1, hu2, hu3⟩ ⟨hv1, hv2, hv3⟩
    refine ⟨fun x y => ?_, fun x y y' a => ?_, fun x x' y b => ?_⟩
    · simp only [Pi.add_apply, Finset.sum_add_distrib, hu1, hv1, add_zero]
    · simp only [Pi.add_apply, Finset.sum_add_distrib, hu2 x y y' a, hv2 x y y' a]
    · simp only [Pi.add_apply, Finset.sum_add_distrib, hu3 x x' y b, hv3 x x' y b]
  zero_mem' := by
    refine ⟨fun x y => ?_, fun x y y' a => ?_, fun x x' y b => ?_⟩ <;> simp
  smul_mem' := by
    rintro c v ⟨hv1, hv2, hv3⟩
    refine ⟨fun x y => ?_, fun x y y' a => ?_, fun x x' y b => ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, hv1, mul_zero]
    · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, hv2 x y y' a]
    · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, hv3 x x' y b]

/-- The `48` coordinates of the source: the joint entries with `a, b < 3`, Alice's marginals with
`a < 3` (context `(x, 0)`) and Bob's with `b < 3` (context `(0, y)`). -/
def bgpCoords : Table (Fin 4) (Fin 4) →ₗ[ℝ]
    ((Fin 2 × Fin 2 × Fin 3 × Fin 3) ⊕ (Fin 2 × Fin 3) ⊕ (Fin 2 × Fin 3) → ℝ) where
  toFun v := Sum.elim (fun e => v e.1 e.2.1 e.2.2.1.castSucc e.2.2.2.castSucc)
    (Sum.elim (fun e => ∑ b, v e.1 0 e.2.castSucc b) (fun e => ∑ a, v 0 e.1 a e.2.castSucc))
  map_add' u v := by
    funext c
    rcases c with e | e | e <;> simp [Finset.sum_add_distrib]
  map_smul' r v := by
    funext c
    rcases c with e | e | e <;> simp [Finset.mul_sum]

/-- A normalized no-signalling direction is determined by the 48 coordinates. -/
theorem bgpCoords_injective :
    Function.Injective (bgpCoords.comp bgpNSDirection.subtype) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  rintro ⟨v, hv1, hv2, hv3⟩ h0
  have hJ : ∀ x y (a b : Fin 3), v x y a.castSucc b.castSucc = 0 := fun x y a b =>
    congrFun h0 (Sum.inl (x, y, a, b))
  have hA : ∀ x (a : Fin 3), ∑ b, v x 0 a.castSucc b = 0 := fun x a =>
    congrFun h0 (Sum.inr (Sum.inl (x, a)))
  have hB : ∀ y (b : Fin 3), ∑ a, v 0 y a b.castSucc = 0 := fun y b =>
    congrFun h0 (Sum.inr (Sum.inr (y, b)))
  have h2 : ∀ x y (a : Fin 3), v x y a.castSucc (Fin.last 3) = 0 := by
    intro x y a
    have hs : ∑ b, v x y a.castSucc b = 0 := (hv2 x y 0 a.castSucc).trans (hA x a)
    rw [Fin.sum_univ_castSucc] at hs
    simp only [hJ, Finset.sum_const_zero, zero_add] at hs
    exact hs
  have h3 : ∀ x y (b : Fin 3), v x y (Fin.last 3) b.castSucc = 0 := by
    intro x y b
    have hs : ∑ a, v x y a b.castSucc = 0 := (hv3 x 0 y b.castSucc).trans (hB y b)
    rw [Fin.sum_univ_castSucc] at hs
    simp only [hJ, Finset.sum_const_zero, zero_add] at hs
    exact hs
  have h4 : ∀ x y, v x y (Fin.last 3) (Fin.last 3) = 0 := by
    intro x y
    have hs := hv1 x y
    rw [Fin.sum_univ_castSucc] at hs
    simp only [Fin.sum_univ_castSucc, hJ, h2, h3, Finset.sum_const_zero, zero_add,
      add_zero] at hs
    exact hs
  apply Subtype.ext
  funext x y a b
  show v x y a b = 0
  rcases Fin.eq_castSucc_or_eq_last a with ⟨a', rfl⟩ | rfl <;>
    rcases Fin.eq_castSucc_or_eq_last b with ⟨b', rfl⟩ | rfl
  · exact hJ x y a' b'
  · exact h2 x y a'
  · exact h3 x y b'
  · exact h4 x y

/-- The normalized no-signalling directions have dimension at most `48`. -/
theorem finrank_bgpNSDirection_le : Module.finrank ℝ bgpNSDirection ≤ 48 := by
  have h := LinearMap.finrank_le_finrank_of_injective bgpCoords_injective
  simpa [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_prod] using h

/-- The difference of two no-signalling behaviours is a normalized no-signalling direction. -/
theorem sub_mem_bgpNSDirection {p q : Table (Fin 4) (Fin 4)} (hp : IsNoSignalling p)
    (hq : IsNoSignalling q) : p - q ∈ bgpNSDirection := by
  refine ⟨fun x y => ?_, fun x y y' a => ?_, fun x x' y b => ?_⟩
  · simp only [Pi.sub_apply, Finset.sum_sub_distrib, hp.isBehaviour.sum_eq_one,
      hq.isBehaviour.sum_eq_one, sub_self]
  · simp only [Pi.sub_apply, Finset.sum_sub_distrib, hp.margA_indep x y y' a,
      hq.margA_indep x y y' a]
  · simp only [Pi.sub_apply, Finset.sum_sub_distrib, hp.margB_indep x x' y b,
      hq.margB_indep x x' y b]

/-- The local polytope `C₄` spans at most the normalized no-signalling directions. -/
theorem vectorSpan_localSet_le :
    vectorSpan ℝ (localSet (Fin 4) (Fin 4)) ≤ bgpNSDirection := by
  rw [vectorSpan_def, Submodule.span_le]
  rintro _ ⟨p, hp, q, hq, rfl⟩
  exact sub_mem_bgpNSDirection (isNoSignalling_of_mem_localSet hp)
    (isNoSignalling_of_mem_localSet hq)

end CGLMPBounds
