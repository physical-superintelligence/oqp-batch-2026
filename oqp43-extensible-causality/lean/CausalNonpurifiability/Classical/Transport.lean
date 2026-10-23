module

public import Mathlib
public import CausalNonpurifiability.Definitions.Causality

@[expose] public section


/-!
# `CausalNonpurifiability.Classical.Transport`

Real-capacity transportation theorem: the rectangle bounds `eq:cut` imply a feasible
split `z` of the outcome table with prescribed marginals (`eq:transport`), and the
resulting ordered components `2z`, `2(p - z)` give a half-causal decomposition
(`eq:causal-components`).  Pure finite real analysis; no quantum imports.

## Proof architecture (manuscript §5, "Construction of the ordered joint distributions")

The manuscript's network `s → v_{ab} → {A_a, B_b} → t` is reduced to the equivalent
three-layer bipartite network

* `s → a` with capacity `rA a` (Alice's endpoint masses),
* `a → b` with capacity `p a b` (the cell mass that may be routed to Alice),
* `b → t` with capacity `c b := (∑ a, p a b) - rB b` (the cell mass that must be
  routed to Alice in column `b`; everything else goes to Bob).

A flow is a table `z` with `0 ≤ z ≤ p`, row sums `≤ rA`, column sums `≤ c`.
The manuscript's compactness argument is followed literally:

1. `Transport.isCompact_feasible` / `Transport.exists_max_flow`: the feasible flows
   form a nonempty compact set, so a flow of maximal value exists
   (`IsCompact.exists_isMaxOn`).
2. `Transport.Reach`: residual reachability from the source (a source edge with
   slack, a forward cell edge with slack, a backward cell edge carrying flow).
3. `Transport.push_of_reach`: along any residual walk to a node one can push
   `ε` units for every sufficiently small `ε > 0` (walks may repeat edges, so the
   perturbation is only controlled by `K·ε`; simple paths are never needed).
4. `Transport.colSum_eq_of_reach`: at a maximal flow no reachable column has sink
   slack, otherwise pushing `ε` increases the value.
5. `Transport.exists_flow_of_cut`: the reachable rows/columns `RA, RB` form the cut
   of `eq:cut`; the cut inequality forces the value to be `∑ rA`, so every row and
   column constraint is saturated.
6. `transport_of_rectangles`: the rectangle bounds `eq:cut` (for the complementary
   rectangle) are exactly the cut inequalities of the three-layer network.
7. `halfCausal_of_transport`, `halfCausal_of_rectangles`, `causal_of_rectangles`:
   `eq:causal-components`.

Manuscript anchors: `eq:cut`, `eq:transport`, `eq:causal-components`.
-/

set_option autoImplicit false

namespace CausalNonpurifiability

namespace Transport

variable {A B : Type} [Fintype A] [Fintype B]

/-- Row sum of a table: the amount routed from cell row `a` to Alice's endpoint `A_a`. -/
def rowSum (z : A → B → ℝ) (a : A) : ℝ := ∑ b, z a b

/-- Column sum of a table. -/
def colSum (z : A → B → ℝ) (b : B) : ℝ := ∑ a, z a b

/-- Total mass of a table (the flow value of the three-layer network). -/
def total (z : A → B → ℝ) : ℝ := ∑ a, ∑ b, z a b

theorem total_eq_sum_rowSum (z : A → B → ℝ) : total z = ∑ a, rowSum z a := rfl

theorem total_eq_sum_colSum (z : A → B → ℝ) : total z = ∑ b, colSum z b := by
  unfold total colSum
  exact Finset.sum_comm

/-- Feasible flows of the three-layer network with source capacities `rA`, cell
capacities `p`, and sink capacities `c` (manuscript §5 network, bipartite form). -/
def Feasible (p : A → B → ℝ) (rA : A → ℝ) (c : B → ℝ) (z : A → B → ℝ) : Prop :=
  (∀ a b, 0 ≤ z a b ∧ z a b ≤ p a b) ∧ (∀ a, rowSum z a ≤ rA a) ∧ (∀ b, colSum z b ≤ c b)

theorem zero_feasible (p : A → B → ℝ) (rA : A → ℝ) (c : B → ℝ)
    (hp : ∀ a b, 0 ≤ p a b) (hrA : ∀ a, 0 ≤ rA a) (hc : ∀ b, 0 ≤ c b) :
    Feasible p rA c (fun _ _ => 0) := by
  refine ⟨fun a b => ⟨le_rfl, hp a b⟩, fun a => ?_, fun b => ?_⟩
  · simpa [rowSum] using hrA a
  · simpa [colSum] using hc b

omit [Fintype A] in
theorem continuous_rowSum (a : A) : Continuous fun z : A → B → ℝ => rowSum z a := by
  unfold rowSum
  exact continuous_finsetSum _ fun b _ => (continuous_apply b).comp (continuous_apply a)

omit [Fintype B] in
theorem continuous_colSum (b : B) : Continuous fun z : A → B → ℝ => colSum z b := by
  unfold colSum
  exact continuous_finsetSum _ fun a _ => (continuous_apply b).comp (continuous_apply a)

theorem continuous_total : Continuous fun z : A → B → ℝ => total z := by
  unfold total
  exact continuous_finsetSum _ fun a _ =>
    continuous_finsetSum _ fun b _ => (continuous_apply b).comp (continuous_apply a)

/-- The feasible flows form a compact set (closed subset of the box `∏ [0, p a b]`). -/
theorem isCompact_feasible (p : A → B → ℝ) (rA : A → ℝ) (c : B → ℝ) :
    IsCompact {z : A → B → ℝ | Feasible p rA c z} := by
  have hbox : IsCompact (Set.pi (Set.univ : Set A) fun a =>
      Set.pi (Set.univ : Set B) fun b => Set.Icc (0 : ℝ) (p a b)) :=
    isCompact_univ_pi fun a => isCompact_univ_pi fun b => isCompact_Icc
  refine hbox.of_isClosed_subset ?_ ?_
  · have hset : {z : A → B → ℝ | Feasible p rA c z} =
        (⋂ a, ⋂ b, ({z : A → B → ℝ | 0 ≤ z a b} ∩ {z : A → B → ℝ | z a b ≤ p a b})) ∩
        ((⋂ a, {z : A → B → ℝ | rowSum z a ≤ rA a}) ∩
          (⋂ b, {z : A → B → ℝ | colSum z b ≤ c b})) := by
      ext z
      simp only [Feasible, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
    rw [hset]
    refine (isClosed_iInter fun a => isClosed_iInter fun b => IsClosed.inter ?_ ?_).inter
      ((isClosed_iInter fun a => ?_).inter (isClosed_iInter fun b => ?_))
    · exact isClosed_le continuous_const ((continuous_apply b).comp (continuous_apply a))
    · exact isClosed_le ((continuous_apply b).comp (continuous_apply a)) continuous_const
    · exact isClosed_le (continuous_rowSum a) continuous_const
    · exact isClosed_le (continuous_colSum b) continuous_const
  · intro z hz
    exact Set.mem_univ_pi.2 fun a => Set.mem_univ_pi.2 fun b => ⟨(hz.1 a b).1, (hz.1 a b).2⟩

/-- A flow of maximal value exists (manuscript: "maximize flow value over the compact
set of feasible flows"). -/
theorem exists_max_flow (p : A → B → ℝ) (rA : A → ℝ) (c : B → ℝ)
    (hp : ∀ a b, 0 ≤ p a b) (hrA : ∀ a, 0 ≤ rA a) (hc : ∀ b, 0 ≤ c b) :
    ∃ z : A → B → ℝ, Feasible p rA c z ∧ ∀ z', Feasible p rA c z' → total z' ≤ total z := by
  have hne : ({z : A → B → ℝ | Feasible p rA c z}).Nonempty :=
    ⟨fun _ _ => 0, zero_feasible p rA c hp hrA hc⟩
  obtain ⟨z, hz, hmax⟩ :=
    (isCompact_feasible p rA c).exists_isMaxOn hne continuous_total.continuousOn
  exact ⟨z, hz, fun z' hz' => isMaxOn_iff.mp hmax z' hz'⟩

/-- Residual reachability from the source in the three-layer network of the flow `z`
(manuscript: "residual source-to-sink path").  `src`: the source edge into `a` has
slack; `fwd`: the cell edge `a → b` has slack; `bwd`: the cell edge `a → b` carries
flow, so it can be traversed backwards. -/
inductive Reach (p : A → B → ℝ) (rA : A → ℝ) (z : A → B → ℝ) : A ⊕ B → Prop
  | src (a : A) : rowSum z a < rA a → Reach p rA z (Sum.inl a)
  | fwd (a : A) (b : B) : Reach p rA z (Sum.inl a) → z a b < p a b → Reach p rA z (Sum.inr b)
  | bwd (a : A) (b : B) : Reach p rA z (Sum.inr b) → 0 < z a b → Reach p rA z (Sum.inl a)

section Bump

variable [DecidableEq A] [DecidableEq B]

/-- Add `ε` to the single cell `(a, b)` of a table. -/
def bump (z : A → B → ℝ) (a : A) (b : B) (ε : ℝ) : A → B → ℝ :=
  fun a' b' => z a' b' + if a' = a ∧ b' = b then ε else 0

omit [Fintype A] [Fintype B] in
theorem bump_self (z : A → B → ℝ) (a : A) (b : B) (ε : ℝ) : bump z a b ε a b = z a b + ε := by
  unfold bump
  rw [if_pos ⟨rfl, rfl⟩]

omit [Fintype A] [Fintype B] in
theorem bump_of_ne (z : A → B → ℝ) (a : A) (b : B) (ε : ℝ) {a' : A} {b' : B}
    (h : ¬ (a' = a ∧ b' = b)) : bump z a b ε a' b' = z a' b' := by
  unfold bump
  rw [if_neg h, add_zero]

omit [Fintype A] in
theorem rowSum_bump (z : A → B → ℝ) (a a' : A) (b : B) (ε : ℝ) :
    rowSum (bump z a b ε) a' = rowSum z a' + if a' = a then ε else 0 := by
  unfold rowSum bump
  rw [Finset.sum_add_distrib]
  congr 1
  by_cases h : a' = a
  · subst h
    simp
  · simp [h]

omit [Fintype B] in
theorem colSum_bump (z : A → B → ℝ) (a : A) (b b' : B) (ε : ℝ) :
    colSum (bump z a b ε) b' = colSum z b' + if b' = b then ε else 0 := by
  unfold colSum bump
  rw [Finset.sum_add_distrib]
  congr 1
  by_cases h : b' = b
  · subst h
    simp
  · simp [h]

/-- The augmentation lemma.  If `v` is residually reachable from the source, then for
some `K` and every sufficiently small `ε > 0` there is a table `z'` within `K·ε` of
`z`, still within the cell capacities and the source capacities, whose column sums
agree with those of `z` except that `ε` units have been delivered to `v`:
at a row node `v = inl a` the row `a` has spare source capacity `ε`, at a column node
`v = inr b` the column sum of `b` has increased by exactly `ε`. -/
theorem push_of_reach {p : A → B → ℝ} {rA : A → ℝ} {c : B → ℝ} {z : A → B → ℝ}
    (hz : Feasible p rA c z) {v : A ⊕ B} (h : Reach p rA z v) :
    ∃ K : ℕ, ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ δ → ∃ z' : A → B → ℝ,
      (∀ a b, 0 ≤ z' a b ∧ z' a b ≤ p a b) ∧
      (∀ a, rowSum z' a ≤ rA a) ∧
      (∀ a b, z a b - K * ε ≤ z' a b ∧ z' a b ≤ z a b + K * ε) ∧
      Sum.elim (fun a => (∀ b, colSum z' b = colSum z b) ∧ rowSum z' a + ε ≤ rA a)
        (fun b => (∀ b', b' ≠ b → colSum z' b' = colSum z b') ∧
          colSum z' b = colSum z b + ε) v := by
  induction h with
  | src a hlt =>
    refine ⟨0, rA a - rowSum z a, by linarith, fun ε hε hεδ => ⟨z, hz.1, hz.2.1, ?_, ?_⟩⟩
    · intro a' b'
      simp
    · dsimp only [Sum.elim_inl]
      exact ⟨fun _ => rfl, by linarith⟩
  | fwd a b _ hlt ih =>
    obtain ⟨K, δ, hδ, hK⟩ := ih
    have hKpos : (0 : ℝ) < (K : ℝ) + 1 := by positivity
    refine ⟨K + 1, min δ ((p a b - z a b) / ((K : ℝ) + 1)),
      lt_min hδ (div_pos (by linarith) hKpos), ?_⟩
    intro ε hε hεδ
    have hεδ' : ε ≤ δ := le_trans hεδ (min_le_left _ _)
    have hεcap : ((K : ℝ) + 1) * ε ≤ p a b - z a b := by
      have h1 : ε ≤ (p a b - z a b) / ((K : ℝ) + 1) := le_trans hεδ (min_le_right _ _)
      rw [le_div_iff₀ hKpos] at h1
      linarith
    obtain ⟨z', hz'bd, hz'row, hz'close, hz'v⟩ := hK ε hε hεδ'
    dsimp only [Sum.elim_inl] at hz'v
    obtain ⟨hcol, hrow⟩ := hz'v
    refine ⟨bump z' a b ε, ?_, ?_, ?_, ?_⟩
    · intro a' b'
      by_cases hab : a' = a ∧ b' = b
      · obtain ⟨rfl, rfl⟩ := hab
        rw [bump_self]
        have h1 := hz'bd a' b'
        have h2 := hz'close a' b'
        constructor <;> linarith
      · rw [bump_of_ne z' a b ε hab]
        exact hz'bd a' b'
    · intro a'
      rw [rowSum_bump]
      by_cases ha : a' = a
      · subst ha
        simp only [if_true]
        linarith
      · simp only [ha, if_false, add_zero]
        exact hz'row a'
    · intro a' b'
      push_cast
      by_cases hab : a' = a ∧ b' = b
      · obtain ⟨rfl, rfl⟩ := hab
        rw [bump_self]
        have h2 := hz'close a' b'
        constructor <;> linarith
      · rw [bump_of_ne z' a b ε hab]
        have h2 := hz'close a' b'
        constructor <;> linarith
    · dsimp only [Sum.elim_inr]
      refine ⟨fun b' hb' => ?_, ?_⟩
      · rw [colSum_bump, if_neg hb', add_zero]
        exact hcol b'
      · rw [colSum_bump, if_pos rfl, hcol b]
  | bwd a b _ hpos ih =>
    obtain ⟨K, δ, hδ, hK⟩ := ih
    have hKpos : (0 : ℝ) < (K : ℝ) + 1 := by positivity
    refine ⟨K + 1, min δ (z a b / ((K : ℝ) + 1)), lt_min hδ (div_pos hpos hKpos), ?_⟩
    intro ε hε hεδ
    have hεδ' : ε ≤ δ := le_trans hεδ (min_le_left _ _)
    have hεcap : ((K : ℝ) + 1) * ε ≤ z a b := by
      have h1 : ε ≤ z a b / ((K : ℝ) + 1) := le_trans hεδ (min_le_right _ _)
      rw [le_div_iff₀ hKpos] at h1
      linarith
    obtain ⟨z', hz'bd, hz'row, hz'close, hz'v⟩ := hK ε hε hεδ'
    dsimp only [Sum.elim_inr] at hz'v
    obtain ⟨hcol, hcolb⟩ := hz'v
    refine ⟨bump z' a b (-ε), ?_, ?_, ?_, ?_⟩
    · intro a' b'
      by_cases hab : a' = a ∧ b' = b
      · obtain ⟨rfl, rfl⟩ := hab
        rw [bump_self]
        have h1 := hz'bd a' b'
        have h2 := hz'close a' b'
        constructor <;> linarith
      · rw [bump_of_ne z' a b (-ε) hab]
        exact hz'bd a' b'
    · intro a'
      rw [rowSum_bump]
      by_cases ha : a' = a
      · subst ha
        simp only [if_true]
        linarith [hz'row a']
      · simp only [ha, if_false, add_zero]
        exact hz'row a'
    · intro a' b'
      push_cast
      by_cases hab : a' = a ∧ b' = b
      · obtain ⟨rfl, rfl⟩ := hab
        rw [bump_self]
        have h2 := hz'close a' b'
        constructor <;> linarith
      · rw [bump_of_ne z' a b (-ε) hab]
        have h2 := hz'close a' b'
        constructor <;> linarith
    · dsimp only [Sum.elim_inl]
      refine ⟨fun b' => ?_, ?_⟩
      · rw [colSum_bump]
        by_cases hb : b' = b
        · subst hb
          simp only [if_true]
          linarith
        · simp only [hb, if_false, add_zero]
          exact hcol b' hb
      · rw [rowSum_bump, if_pos rfl]
        linarith [hz'row a]

/-- At a maximal flow, every residually reachable column is saturated at the sink
(manuscript: "there could be no residual source-to-sink path, since such a path
would increase it"). -/
theorem colSum_eq_of_reach {p : A → B → ℝ} {rA : A → ℝ} {c : B → ℝ} {z : A → B → ℝ}
    (hz : Feasible p rA c z) (hmax : ∀ z', Feasible p rA c z' → total z' ≤ total z)
    {b : B} (h : Reach p rA z (Sum.inr b)) : colSum z b = c b := by
  by_contra hne
  have hlt : colSum z b < c b := lt_of_le_of_ne (hz.2.2 b) hne
  obtain ⟨K, δ, hδ, hK⟩ := push_of_reach hz h
  have hε : 0 < min δ (c b - colSum z b) := lt_min hδ (by linarith)
  obtain ⟨z', hz'bd, hz'row, -, hz'v⟩ := hK _ hε (min_le_left _ _)
  dsimp only [Sum.elim_inr] at hz'v
  obtain ⟨hcol, hcolb⟩ := hz'v
  have hfeas : Feasible p rA c z' := by
    refine ⟨hz'bd, hz'row, fun b' => ?_⟩
    by_cases hb : b' = b
    · subst hb
      rw [hcolb]
      linarith [min_le_right δ (c b' - colSum z b')]
    · rw [hcol b' hb]
      exact hz.2.2 b'
  have hcol' : ∀ b', colSum z' b' = colSum z b' + if b' = b then min δ (c b - colSum z b) else 0 := by
    intro b'
    by_cases hb : b' = b
    · subst hb
      simp [hcolb]
    · simp [hb, hcol b' hb]
  have htot : total z' = total z + min δ (c b - colSum z b) := by
    rw [total_eq_sum_colSum, total_eq_sum_colSum]
    simp only [hcol', Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have := hmax z' hfeas
  linarith

/-- Max-flow/min-cut for the three-layer network: the cut inequalities
`rA(S) ≤ c(T) + p(S × Tᶜ)` (for all `S, T`) and the balance `∑ rA = ∑ c` give a flow
saturating every source and sink edge.  Proof: take a maximal flow; the residually
reachable rows `RA` and columns `RB` form a cut whose capacity equals the flow value,
so the cut inequality at `(RA, RB)` forces value `= ∑ rA`. -/
theorem exists_flow_of_cut (p : A → B → ℝ) (rA : A → ℝ) (c : B → ℝ)
    (hp : ∀ a b, 0 ≤ p a b) (hrA : ∀ a, 0 ≤ rA a) (hc : ∀ b, 0 ≤ c b)
    (hsum : ∑ a, rA a = ∑ b, c b)
    (hcut : ∀ (S : Finset A) (T : Finset B),
      ∑ a ∈ S, rA a ≤ (∑ b ∈ T, c b) + ∑ a ∈ S, ∑ b ∈ Tᶜ, p a b) :
    ∃ z : A → B → ℝ, (∀ a b, 0 ≤ z a b ∧ z a b ≤ p a b) ∧
      (∀ a, ∑ b, z a b = rA a) ∧ (∀ b, ∑ a, z a b = c b) := by
  classical
  obtain ⟨z, hz, hmax⟩ := exists_max_flow p rA c hp hrA hc
  obtain ⟨RA, memRA⟩ : ∃ RA : Finset A, ∀ a, a ∈ RA ↔ Reach p rA z (Sum.inl a) :=
    ⟨Finset.univ.filter fun a => Reach p rA z (Sum.inl a), fun a => by simp⟩
  obtain ⟨RB, memRB⟩ : ∃ RB : Finset B, ∀ b, b ∈ RB ↔ Reach p rA z (Sum.inr b) :=
    ⟨Finset.univ.filter fun b => Reach p rA z (Sum.inr b), fun b => by simp⟩
  -- unreachable rows are saturated at the source
  have F1 : ∀ a, a ∉ RA → rowSum z a = rA a := by
    intro a ha
    refine le_antisymm (hz.2.1 a) (not_lt.mp fun hlt => ha ((memRA a).2 (Reach.src a hlt)))
  -- cells from reachable rows to unreachable columns are saturated
  have F2 : ∀ a ∈ RA, ∀ b, b ∉ RB → z a b = p a b := by
    intro a ha b hb
    exact le_antisymm (hz.1 a b).2
      (not_lt.mp fun hlt => hb ((memRB b).2 (Reach.fwd a b ((memRA a).1 ha) hlt)))
  -- cells from unreachable rows to reachable columns carry no flow
  have F3 : ∀ a, a ∉ RA → ∀ b ∈ RB, z a b = 0 := by
    intro a ha b hb
    exact le_antisymm
      (not_lt.mp fun hlt => ha ((memRA a).2 (Reach.bwd a b ((memRB b).1 hb) hlt)))
      (hz.1 a b).1
  -- reachable columns are saturated at the sink (maximality)
  have F4 : ∀ b ∈ RB, colSum z b = c b :=
    fun b hb => colSum_eq_of_reach hz hmax ((memRB b).1 hb)
  have hcutR := hcut RA RB
  have h1 : ∑ b ∈ RB, c b = ∑ a ∈ RA, ∑ b ∈ RB, z a b := by
    calc ∑ b ∈ RB, c b = ∑ b ∈ RB, colSum z b :=
          Finset.sum_congr rfl fun b hb => (F4 b hb).symm
      _ = ∑ b ∈ RB, ∑ a, z a b := rfl
      _ = ∑ a, ∑ b ∈ RB, z a b := Finset.sum_comm
      _ = ∑ a ∈ RA, ∑ b ∈ RB, z a b + ∑ a ∈ RAᶜ, ∑ b ∈ RB, z a b :=
          (Finset.sum_add_sum_compl RA _).symm
      _ = ∑ a ∈ RA, ∑ b ∈ RB, z a b := by
          have h0 : ∑ a ∈ RAᶜ, ∑ b ∈ RB, z a b = 0 :=
            Finset.sum_eq_zero fun a ha =>
              Finset.sum_eq_zero fun b hb => F3 a (Finset.mem_compl.mp ha) b hb
          rw [h0, add_zero]
  have h2 : ∑ a ∈ RA, ∑ b ∈ RBᶜ, p a b = ∑ a ∈ RA, ∑ b ∈ RBᶜ, z a b :=
    Finset.sum_congr rfl fun a ha =>
      Finset.sum_congr rfl fun b hb => (F2 a ha b (Finset.mem_compl.mp hb)).symm
  have h3 : ∑ a ∈ RA, rowSum z a =
      ∑ a ∈ RA, ∑ b ∈ RB, z a b + ∑ a ∈ RA, ∑ b ∈ RBᶜ, z a b := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => (Finset.sum_add_sum_compl RB _).symm
  have h4 : ∑ a ∈ RAᶜ, rowSum z a = ∑ a ∈ RAᶜ, rA a :=
    Finset.sum_congr rfl fun a ha => F1 a (Finset.mem_compl.mp ha)
  have e1 := Finset.sum_add_sum_compl RA rA
  have e2 := Finset.sum_add_sum_compl RA (rowSum z)
  have htr : total z = ∑ a, rowSum z a := total_eq_sum_rowSum z
  have htc : total z = ∑ b, colSum z b := total_eq_sum_colSum z
  have htotal_le : total z ≤ ∑ a, rA a := Finset.sum_le_sum fun a _ => hz.2.1 a
  have htotal_ge : ∑ a, rA a ≤ total z := by linarith
  have hrow : ∀ a, rowSum z a = rA a := by
    have h0 : ∑ a, (rA a - rowSum z a) = 0 := by
      rw [Finset.sum_sub_distrib]
      linarith
    have h5 := (Finset.sum_eq_zero_iff_of_nonneg fun a _ => sub_nonneg.mpr (hz.2.1 a)).mp h0
    intro a
    linarith [h5 a (Finset.mem_univ a)]
  have hcol : ∀ b, colSum z b = c b := by
    have h0 : ∑ b, (c b - colSum z b) = 0 := by
      rw [Finset.sum_sub_distrib]
      linarith
    have h5 := (Finset.sum_eq_zero_iff_of_nonneg fun b _ => sub_nonneg.mpr (hz.2.2 b)).mp h0
    intro b
    linarith [h5 b (Finset.mem_univ b)]
  exact ⟨z, hz.1, hrow, hcol⟩

end Bump

end Transport

-- `hrB` is part of the statement but is implied by `hrect ∅ {b}`,
-- so the proof never uses it; the unused-variable linter is silenced for this declaration only.
set_option linter.unusedVariables false in
/-- **Transportation theorem** (`eq:transport` from `eq:cut`).  For a normalized
nonnegative outcome table `p` and endpoint masses `rA`, `rB` of total `1/2` each,
the rectangle bounds `p(S × T) ≤ rA(S) + rB(T)` for all `S, T` yield a split
`0 ≤ z ≤ p` routing `rA a` to each Alice endpoint (row sums of `z`) and `rB b` to
each Bob endpoint (column sums of `p - z`). -/
theorem transport_of_rectangles
    {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (p : A → B → ℝ) (rA : A → ℝ) (rB : B → ℝ)
    (hp : ∀ a b, 0 ≤ p a b)
    (hrA : ∀ a, 0 ≤ rA a) (hrB : ∀ b, 0 ≤ rB b)
    (htotal : ∑ a, ∑ b, p a b = 1)
    (hmA : ∑ a, rA a = 1 / 2)
    (hmB : ∑ b, rB b = 1 / 2)
    (hrect : ∀ (S : Finset A) (T : Finset B),
      (∑ a ∈ S, ∑ b ∈ T, p a b) ≤
        (∑ a ∈ S, rA a) + ∑ b ∈ T, rB b) :
    ∃ z : A → B → ℝ,
      (∀ a b, 0 ≤ z a b ∧ z a b ≤ p a b) ∧
      (∀ a, ∑ b, z a b = rA a) ∧
      (∀ b, ∑ a, (p a b - z a b) = rB b) := by
  -- sink capacities: the column mass that must be routed to Alice
  obtain ⟨c, hc⟩ : ∃ c : B → ℝ, ∀ b, c b = (∑ a, p a b) - rB b := ⟨_, fun b => rfl⟩
  -- the rectangle bound for the complementary rectangle is the cut inequality
  have hcut : ∀ (S : Finset A) (T : Finset B),
      ∑ a ∈ S, rA a ≤ (∑ b ∈ T, c b) + ∑ a ∈ S, ∑ b ∈ Tᶜ, p a b := by
    intro S T
    have e1 := Finset.sum_add_sum_compl S rA
    have e2 := Finset.sum_add_sum_compl T rB
    have hsplit : ∀ a, ∑ b, p a b = ∑ b ∈ T, p a b + ∑ b ∈ Tᶜ, p a b :=
      fun a => (Finset.sum_add_sum_compl T (p a)).symm
    have e3 : ∑ a, ∑ b, p a b =
        (∑ a ∈ S, ∑ b ∈ T, p a b + ∑ a ∈ S, ∑ b ∈ Tᶜ, p a b) +
        (∑ a ∈ Sᶜ, ∑ b ∈ T, p a b + ∑ a ∈ Sᶜ, ∑ b ∈ Tᶜ, p a b) := by
      have e0 : ∑ a ∈ S, ∑ b, p a b + ∑ a ∈ Sᶜ, ∑ b, p a b = ∑ a, ∑ b, p a b :=
        Finset.sum_add_sum_compl S _
      rw [← e0]
      simp only [hsplit, Finset.sum_add_distrib]
    have e5 : ∑ b ∈ T, ∑ a, p a b = ∑ a ∈ S, ∑ b ∈ T, p a b + ∑ a ∈ Sᶜ, ∑ b ∈ T, p a b := by
      rw [Finset.sum_comm]
      exact (Finset.sum_add_sum_compl S _).symm
    have e4 : ∑ b ∈ T, c b =
        (∑ a ∈ S, ∑ b ∈ T, p a b + ∑ a ∈ Sᶜ, ∑ b ∈ T, p a b) - ∑ b ∈ T, rB b := by
      rw [← e5, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun b _ => hc b
    have hr := hrect Sᶜ Tᶜ
    linarith
  have hcnn : ∀ b, 0 ≤ c b := by
    intro b
    have h := hcut ∅ {b}
    simpa using h
  have hsum : ∑ a, rA a = ∑ b, c b := by
    have h : ∑ b, c b = ∑ b, ∑ a, p a b - ∑ b, rB b := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun b _ => hc b
    rw [h, Finset.sum_comm, htotal, hmB, hmA]
    norm_num
  obtain ⟨z, hzbd, hrow, hcol⟩ := Transport.exists_flow_of_cut p rA c hp hrA hcnn hsum hcut
  refine ⟨z, hzbd, hrow, fun b => ?_⟩
  rw [Finset.sum_sub_distrib, hcol b, hc b]
  ring

/-- `eq:causal-components`: given, for every setting pair `(x, y)`, a transport `z`
for the table `p x y` with the fixed endpoint arrays `rA x`, `rB y` of mass `1/2`,
the tables `2z` and `2(p - z)` are normalized, respectively non-signalling from Bob
to Alice and from Alice to Bob, and `p = ½·2z + ½·2(p - z)`; hence `p` is half-causal.
The endpoint arrays are the same across all settings, which is what makes the
componentwise marginals setting-independent. -/
theorem halfCausal_of_transport {X Y A B : Type} [Fintype A] [Fintype B]
    (p : Prob X Y A B) (rA : X → A → ℝ) (rB : Y → B → ℝ)
    (hmA : ∀ x, ∑ a, rA x a = 1 / 2) (hmB : ∀ y, ∑ b, rB y b = 1 / 2)
    (htr : ∀ x y, ∃ z : A → B → ℝ,
      (∀ a b, 0 ≤ z a b ∧ z a b ≤ p x y a b) ∧
      (∀ a, ∑ b, z a b = rA x a) ∧
      (∀ b, ∑ a, (p x y a b - z a b) = rB y b)) :
    HalfCausal p := by
  choose z hz using htr
  refine ⟨fun x y a b => 2 * z x y a b, fun x y a b => 2 * (p x y a b - z x y a b),
    ⟨fun x y a b => ?_, fun x y => ?_⟩, ⟨fun x y a b => ?_, fun x y => ?_⟩, ?_, ?_, ?_⟩
  · have := (hz x y).1 a b
    linarith
  · simp only [← Finset.mul_sum, (hz x y).2.1, hmA x]
    norm_num
  · have := (hz x y).1 a b
    linarith
  · rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, (hz x y).2.2, hmB y]
    norm_num
  · intro x y y' a
    simp only [← Finset.mul_sum, (hz x y).2.1, (hz x y').2.1]
  · intro x x' y b
    simp only [← Finset.mul_sum, (hz x y).2.2, (hz x' y).2.2]
  · intro x y a b
    ring

/-- Rectangle bounds `eq:cut` for every setting pair, with setting-local endpoint
arrays of mass `1/2`, give a half-causal decomposition (`eq:causal-components`). -/
theorem halfCausal_of_rectangles {X Y A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (p : Prob X Y A B) (rA : X → A → ℝ) (rB : Y → B → ℝ)
    (hp : ∀ x y a b, 0 ≤ p x y a b)
    (hrA : ∀ x a, 0 ≤ rA x a) (hrB : ∀ y b, 0 ≤ rB y b)
    (htotal : ∀ x y, ∑ a, ∑ b, p x y a b = 1)
    (hmA : ∀ x, ∑ a, rA x a = 1 / 2) (hmB : ∀ y, ∑ b, rB y b = 1 / 2)
    (hrect : ∀ x y (S : Finset A) (T : Finset B),
      (∑ a ∈ S, ∑ b ∈ T, p x y a b) ≤ (∑ a ∈ S, rA x a) + ∑ b ∈ T, rB y b) :
    HalfCausal p :=
  halfCausal_of_transport p rA rB hmA hmB fun x y =>
    transport_of_rectangles (p x y) (rA x) (rB y) (hp x y) (hrA x) (hrB y) (htotal x y)
      (hmA x) (hmB y) (hrect x y)

/-- Rectangle bounds for every setting pair give a causal distribution
(`eq:causal-definition` with `λ = 1/2`). -/
theorem causal_of_rectangles {X Y A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (p : Prob X Y A B) (rA : X → A → ℝ) (rB : Y → B → ℝ)
    (hp : ∀ x y a b, 0 ≤ p x y a b)
    (hrA : ∀ x a, 0 ≤ rA x a) (hrB : ∀ y b, 0 ≤ rB y b)
    (htotal : ∀ x y, ∑ a, ∑ b, p x y a b = 1)
    (hmA : ∀ x, ∑ a, rA x a = 1 / 2) (hmB : ∀ y, ∑ b, rB y b = 1 / 2)
    (hrect : ∀ x y (S : Finset A) (T : Finset B),
      (∑ a ∈ S, ∑ b ∈ T, p x y a b) ≤ (∑ a ∈ S, rA x a) + ∑ b ∈ T, rB y b) :
    Causal p :=
  halfCausal_causal (halfCausal_of_rectangles p rA rB hp hrA hrB htotal hmA hmB hrect)

end CausalNonpurifiability
