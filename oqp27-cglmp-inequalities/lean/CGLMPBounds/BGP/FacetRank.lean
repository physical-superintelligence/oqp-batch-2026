module

public import CGLMPBounds.BGP.Rank

@[expose] public section


/-!
# Proposition G.1: (G.1) defines a facet of `C₄`

Supplement, Proposition G.1: "Inequality (G.1) defines a facet of `C₄` …"; proof: "Evaluation on the
`4⁴` strategies gives Table G.1, proving local validity", "The affine dimension is 48", and the minor
(G.2) of Table G.2: "Thus the saturation face has affine rank 47."

* `bgpLin` : `F` as a linear functional (`bgpLin_apply`);
* `bgpFunctional_detTable` : `F(q_s)` is the integer `bgpDetVal s`;
* `bgpFunctional_nonpos_of_mem_localSet` : `F ≤ 0` on `C₄` (all `256` deterministic values are
  `≤ 0`);
* `bgp_facet_spec` : `dim C₄ = 48`, `dim (C₄ ∩ {F = 0}) = 47`, and `F ≤ 0` on `C₄`.

The dimension count: the 48 affinely independent saturators of Table G.2
(`bgp_rank_saturators_affineIndependent`) give `dim (C₄ ∩ {F = 0}) ≥ 47`. The face lies in the
kernel of `F` within the normalized no-signalling directions, which have dimension at most `48`
(`finrank_bgpNSDirection_le`), and `F` is not constant on `C₄`. Hence the face has dimension exactly
`47` and `C₄` exactly `48`.
-/

namespace CGLMPBounds

open Finset

/-! ### `F` is linear -/

/-- The entry `q ↦ q(a,b|x,y)` as a linear functional. -/
def bgpEntryLin (x y : Fin 2) (a b : Fin 4) : Table (Fin 4) (Fin 4) →ₗ[ℝ] ℝ where
  toFun p := p x y a b
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem bgpEntryLin_apply (x y : Fin 2) (a b : Fin 4) (p : Table (Fin 4) (Fin 4)) :
    bgpEntryLin x y a b p = p x y a b := rfl

/-- `F` as a linear functional. -/
noncomputable def bgpLin : Table (Fin 4) (Fin 4) →ₗ[ℝ] ℝ :=
  (∑ x : Fin 2, ∑ a : Fin 3,
      (bgpL (bgpIndex x a) : ℝ) • ∑ b : Fin 4, bgpEntryLin x 0 a.castSucc b)
    + (∑ y : Fin 2, ∑ b : Fin 3,
      (bgpL (bgpIndex y b) : ℝ) • ∑ a : Fin 4, bgpEntryLin 0 y a b.castSucc)
    + ∑ x : Fin 2, ∑ y : Fin 2, ∑ a : Fin 3, ∑ b : Fin 3,
        (bgpH (bgpIndex x a) (bgpIndex y b) : ℝ) • bgpEntryLin x y a.castSucc b.castSucc

theorem bgpLin_apply (p : Table (Fin 4) (Fin 4)) : bgpLin p = bgpFunctional p := by
  simp only [bgpLin, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    bgpEntryLin_apply]
  rfl

theorem bgpFunctional_sub (p q : Table (Fin 4) (Fin 4)) :
    bgpFunctional (p - q) = bgpFunctional p - bgpFunctional q := by
  rw [← bgpLin_apply, ← bgpLin_apply, ← bgpLin_apply, map_sub]

/-! ### `F` on deterministic tables -/

/-- `F(q_s)` as an integer: `ℓ · A(s) + ℓ · B(s) + A(s)ᵀ H B(s)`. -/
def bgpDetVal (s : Strategy (Fin 4) (Fin 4)) : ℤ :=
  (∑ x : Fin 2, ∑ a : Fin 3, bgpL (bgpIndex x a) * (if a.castSucc = s.1 x then 1 else 0))
    + (∑ y : Fin 2, ∑ b : Fin 3, bgpL (bgpIndex y b) * (if b.castSucc = s.2 y then 1 else 0))
    + ∑ x : Fin 2, ∑ y : Fin 2, ∑ a : Fin 3, ∑ b : Fin 3, bgpH (bgpIndex x a) (bgpIndex y b)
        * ((if a.castSucc = s.1 x then 1 else 0) * (if b.castSucc = s.2 y then 1 else 0))

theorem detTable_eq_mul (s : Strategy (Fin 4) (Fin 4)) (x y : Fin 2) (a b : Fin 4) :
    detTable s x y a b
      = (if a = s.1 x then (1 : ℝ) else 0) * (if b = s.2 y then (1 : ℝ) else 0) := by
  unfold detTable
  by_cases ha : a = s.1 x <;> by_cases hb : b = s.2 y <;> simp [ha, hb]

theorem bgpFunctional_detTable (s : Strategy (Fin 4) (Fin 4)) :
    bgpFunctional (detTable s) = (bgpDetVal s : ℝ) := by
  unfold bgpFunctional bgpDetVal
  -- the marginal sums first, then the joint entries
  simp only [sum_detTable_right, sum_detTable_left]
  simp only [detTable_eq_mul]
  push_cast
  try rfl

/-- Every deterministic strategy, written by its four outcomes. -/
theorem strategy_eq_mk (s : Strategy (Fin 4) (Fin 4)) :
    s = (![s.1 0, s.1 1], ![s.2 0, s.2 1]) := by
  ext x <;> fin_cases x <;> rfl

theorem bgpDetVal_nonpos_mk : ∀ a₀ a₁ b₀ b₁ : Fin 4,
    bgpDetVal (![a₀, a₁], ![b₀, b₁]) ≤ 0 := by
  decide +kernel

theorem bgpDetVal_rank : ∀ i : Fin 48, bgpDetVal (bgpRankStrategy i) = 0 := by
  decide +kernel

theorem bgpDetVal_zero : bgpDetVal (![0, 0], ![0, 0]) = -1 := by
  decide +kernel

/-- **Local validity.** `F ≤ 0` on `C₄`. -/
theorem bgpFunctional_nonpos_of_mem_localSet {q : Table (Fin 4) (Fin 4)}
    (hq : q ∈ localSet (Fin 4) (Fin 4)) : bgpFunctional q ≤ 0 := by
  have hconv : Convex ℝ {p : Table (Fin 4) (Fin 4) | bgpLin p ≤ 0} :=
    convex_halfSpace_le bgpLin.isLinear 0
  have hsub : Set.range (detTable (α := Fin 4) (β := Fin 4))
      ⊆ {p : Table (Fin 4) (Fin 4) | bgpLin p ≤ 0} := by
    rintro _ ⟨s, rfl⟩
    show bgpLin (detTable s) ≤ 0
    rw [bgpLin_apply, bgpFunctional_detTable, strategy_eq_mk s]
    exact_mod_cast bgpDetVal_nonpos_mk (s.1 0) (s.1 1) (s.2 0) (s.2 1)
  have h := convexHull_min hsub hconv hq
  rw [Set.mem_setOf_eq, bgpLin_apply] at h
  exact h

/-! ### The dimensions -/

theorem detTable_mem_localSet (s : Strategy (Fin 4) (Fin 4)) :
    detTable s ∈ localSet (Fin 4) (Fin 4) :=
  subset_convexHull ℝ _ ⟨s, rfl⟩

/-- The saturation face lies in the kernel of `F` within the no-signalling directions. -/
theorem vectorSpan_face_le :
    vectorSpan ℝ (localSet (Fin 4) (Fin 4) ∩ {q | bgpFunctional q = 0})
      ≤ bgpNSDirection ⊓ LinearMap.ker bgpLin := by
  rw [vectorSpan_def, Submodule.span_le]
  rintro _ ⟨p, ⟨hp, hp0⟩, q, ⟨hq, hq0⟩, rfl⟩
  refine ⟨sub_mem_bgpNSDirection (isNoSignalling_of_mem_localSet hp)
    (isNoSignalling_of_mem_localSet hq), ?_⟩
  show bgpLin (p -ᵥ q) = 0
  have hp0' : bgpFunctional p = 0 := hp0
  have hq0' : bgpFunctional q = 0 := hq0
  rw [vsub_eq_sub, bgpLin_apply, bgpFunctional_sub, hp0', hq0', sub_self]

/-- The difference `q_{(0,0,0,0)} - q_{s₀}` of a deterministic table with `F = -1` and a saturator. -/
theorem bgpLin_witness :
    bgpLin (detTable (![0, 0], ![0, 0]) - detTable (bgpRankStrategy 0)) = -1 := by
  rw [bgpLin_apply, bgpFunctional_sub, bgpFunctional_detTable, bgpFunctional_detTable,
    bgpDetVal_zero, bgpDetVal_rank]
  norm_num

/-- **Proposition G.1, facet part.** `dim C₄ = 48`, the saturation face has dimension `47`, and
`F ≤ 0` on `C₄`. -/
theorem bgp_facet_spec :
    Module.finrank ℝ (vectorSpan ℝ (localSet (Fin 4) (Fin 4))) = 48 ∧
      Module.finrank ℝ (vectorSpan ℝ (localSet (Fin 4) (Fin 4) ∩ {q | bgpFunctional q = 0})) = 47 ∧
      ∀ q ∈ localSet (Fin 4) (Fin 4), bgpFunctional q ≤ 0 := by
  set S := localSet (Fin 4) (Fin 4) with hS
  set Fc := S ∩ {q : Table (Fin 4) (Fin 4) | bgpFunctional q = 0} with hFc
  set u := detTable (![0, 0], ![0, 0]) - detTable (bgpRankStrategy 0) with hu
  have hW := finrank_bgpNSDirection_le
  -- the saturators span 47 dimensions inside the face
  have hsat : Set.range (fun i : Fin 48 => detTable (bgpRankStrategy i)) ⊆ Fc := by
    rintro _ ⟨i, rfl⟩
    refine ⟨detTable_mem_localSet _, ?_⟩
    show bgpFunctional (detTable (bgpRankStrategy i)) = 0
    rw [bgpFunctional_detTable, bgpDetVal_rank, Int.cast_zero]
  have h47 : Module.finrank ℝ (vectorSpan ℝ
      (Set.range (fun i : Fin 48 => detTable (bgpRankStrategy i)))) = 47 :=
    bgp_rank_saturators_affineIndependent.finrank_vectorSpan (by simp)
  have hge : 47 ≤ Module.finrank ℝ (vectorSpan ℝ Fc) := by
    rw [← h47]
    exact Submodule.finrank_mono (vectorSpan_mono ℝ hsat)
  -- the face lies in a proper subspace of the no-signalling directions
  have huW : u ∈ bgpNSDirection :=
    sub_mem_bgpNSDirection
      (isNoSignalling_of_mem_localSet (detTable_mem_localSet (![0, 0], ![0, 0])))
      (isNoSignalling_of_mem_localSet (detTable_mem_localSet (bgpRankStrategy 0)))
  have hlt : bgpNSDirection ⊓ LinearMap.ker bgpLin < bgpNSDirection := by
    refine lt_of_le_of_ne inf_le_left (fun h => ?_)
    have hu' : u ∈ bgpNSDirection ⊓ LinearMap.ker bgpLin := by
      rw [h]
      exact huW
    have h0 : bgpLin u = 0 := hu'.2
    rw [hu, bgpLin_witness] at h0
    norm_num at h0
  have hK : Module.finrank ℝ ↥(bgpNSDirection ⊓ LinearMap.ker bgpLin) ≤ 47 := by
    have := Submodule.finrank_lt_finrank_of_lt hlt
    omega
  have hle : Module.finrank ℝ (vectorSpan ℝ Fc) ≤ 47 :=
    (Submodule.finrank_mono vectorSpan_face_le).trans hK
  have hface : Module.finrank ℝ (vectorSpan ℝ Fc) = 47 := le_antisymm hle hge
  -- `C₄` is one dimension larger
  have hFS : vectorSpan ℝ Fc < vectorSpan ℝ S := by
    refine lt_of_le_of_ne (vectorSpan_mono ℝ Set.inter_subset_left) (fun h => ?_)
    have hmem : u ∈ vectorSpan ℝ S :=
      vsub_mem_vectorSpan ℝ (detTable_mem_localSet (![0, 0], ![0, 0]))
        (detTable_mem_localSet (bgpRankStrategy 0))
    rw [← h] at hmem
    have h0 : bgpLin u = 0 := (vectorSpan_face_le hmem).2
    rw [hu, bgpLin_witness] at h0
    norm_num at h0
  have hgt := Submodule.finrank_lt_finrank_of_lt hFS
  have hSle : Module.finrank ℝ (vectorSpan ℝ S) ≤ 48 :=
    (Submodule.finrank_mono vectorSpan_localSet_le).trans hW
  refine ⟨by omega, hface, fun q hq => bgpFunctional_nonpos_of_mem_localSet hq⟩

end CGLMPBounds
