module

public import Mathlib
public import CausalNonpurifiability.Definitions.Instruments
public import CausalNonpurifiability.Definitions.Causality

@[expose] public section


/-!
# `CausalNonpurifiability.Definitions.ExtensibleGeneral`

Extensible causality over **arbitrary** finite ancilla spaces and finite setting/outcome alphabets
(manuscript §2.2, Oreshkov–Giarmatzi Def. 3.2: "every pair of finite ancillary spaces, every
density operator, every collection of local instruments"), and its equivalence with the
`Fin`-indexed quantifier `ExtensiblyCausal` of `Definitions/Instruments`.

* `ExtensiblyCausalGen D W` quantifies over types `RA RB X Y A B` with only the structurally
  necessary instances `[Fintype RA] [DecidableEq RA] [Fintype RB] [DecidableEq RB] [Fintype X]
  [Fintype Y] [Fintype A] [Fintype B]`.  No `Nonempty` assumption is needed: empty settings make
  `Causal` vacuous (`causal_of_isEmpty_left/right`), an empty ancilla contradicts `Tr σ = 1`, and
  an empty outcome alphabet contradicts the instrument normalization.  Finiteness of the setting
  alphabets is used for the transport to `Fin` shapes.
* `extensiblyCausal_iff_gen : ExtensiblyCausal D W ↔ ExtensiblyCausalGen D W`.  `⇐` is
  instantiation; `⇒` reindexes along `Fintype.equivFinOfCardEq` (`Instrument.reindex`,
  `Density.reindex`, `bornExtended_reindex`) and pulls `Causal` back along the relabeling of
  settings and outcomes (`Causal.of_relabel`).

Manuscript anchors: §2.2 (extensible causality), `eq:born`, `eq:causal-definition`.
-/

set_option autoImplicit false

open Matrix
open scoped ComplexOrder Kronecker

namespace CausalNonpurifiability

/-! ### Relabeling settings and outcomes -/

section Relabel

variable {X Y A B X' Y' A' B' : Type}

/-- Relabel a distribution along bijections of settings and outcomes. -/
def Prob.relabel (eX : X ≃ X') (eY : Y ≃ Y') (eA : A ≃ A') (eB : B ≃ B') (p : Prob X Y A B) :
    Prob X' Y' A' B' :=
  fun x y a b => p (eX.symm x) (eY.symm y) (eA.symm a) (eB.symm b)

/-- Causality (`eq:causal-definition`) pulls back along a bijective relabeling of settings and
outcomes: the components are relabeled the same way, `λ` is unchanged. -/
theorem Causal.of_relabel [Fintype A] [Fintype B] [Fintype A'] [Fintype B'] (eX : X ≃ X')
    (eY : Y ≃ Y') (eA : A ≃ A') (eB : B ≃ B') {p : Prob X Y A B}
    (h : Causal (Prob.relabel eX eY eA eB p)) : Causal p := by
  obtain ⟨lam, qAB, qBA, h0, h1, hcAB, hcBA, hnsAB, hnsBA, hmix⟩ := h
  refine ⟨lam, fun x y a b => qAB (eX x) (eY y) (eA a) (eB b),
    fun x y a b => qBA (eX x) (eY y) (eA a) (eB b), h0, h1, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨fun x y a b => hcAB.1 _ _ _ _, fun x y => ?_⟩
    rw [← hcAB.2 (eX x) (eY y), ← Equiv.sum_comp eA]
    exact Finset.sum_congr rfl fun a _ => Equiv.sum_comp eB _
  · refine ⟨fun x y a b => hcBA.1 _ _ _ _, fun x y => ?_⟩
    rw [← hcBA.2 (eX x) (eY y), ← Equiv.sum_comp eA]
    exact Finset.sum_congr rfl fun a _ => Equiv.sum_comp eB _
  · intro x y y' a
    rw [Equiv.sum_comp eB, Equiv.sum_comp eB]
    exact hnsAB _ _ _ _
  · intro x x' y b
    show ∑ a, qBA (eX x) (eY y) (eA a) (eB b) = ∑ a, qBA (eX x') (eY y) (eA a) (eB b)
    rw [Equiv.sum_comp eA (fun a' => qBA (eX x) (eY y) a' (eB b)),
      Equiv.sum_comp eA (fun a' => qBA (eX x') (eY y) a' (eB b))]
    exact hnsBA _ _ _ _
  · intro x y a b
    have := hmix (eX x) (eY y) (eA a) (eB b)
    simpa [Prob.relabel] using this

/-- With no settings for Alice every distribution is (vacuously) causal. -/
theorem causal_of_isEmpty_left [Fintype A] [Fintype B] [IsEmpty X] (p : Prob X Y A B) :
    Causal p :=
  ⟨1 / 2, p, p, by norm_num, by norm_num,
    ⟨fun x => (IsEmpty.false x).elim, fun x => (IsEmpty.false x).elim⟩,
    ⟨fun x => (IsEmpty.false x).elim, fun x => (IsEmpty.false x).elim⟩,
    fun x => (IsEmpty.false x).elim, fun x => (IsEmpty.false x).elim,
    fun x => (IsEmpty.false x).elim⟩

/-- With no settings for Bob every distribution is (vacuously) causal. -/
theorem causal_of_isEmpty_right [Fintype A] [Fintype B] [IsEmpty Y] (p : Prob X Y A B) :
    Causal p :=
  ⟨1 / 2, p, p, by norm_num, by norm_num,
    ⟨fun _ y => (IsEmpty.false y).elim, fun _ y => (IsEmpty.false y).elim⟩,
    ⟨fun _ y => (IsEmpty.false y).elim, fun _ y => (IsEmpty.false y).elim⟩,
    fun _ y => (IsEmpty.false y).elim, fun _ _ y => (IsEmpty.false y).elim,
    fun _ y => (IsEmpty.false y).elim⟩

end Relabel

/-! ### Reindexing ancillas, states and instruments -/

section Reindex

/-- Reindexing commutes with finite sums of matrices. -/
theorem reindex_sum {ι m n m' n' : Type} (s : Finset ι) (e₁ : m ≃ m') (e₂ : n ≃ n')
    (f : ι → Matrix m n ℂ) :
    Matrix.reindex e₁ e₂ (∑ i ∈ s, f i) = ∑ i ∈ s, Matrix.reindex e₁ e₂ (f i) := by
  ext i j
  simp [Matrix.reindex_apply, Matrix.sum_apply]

/-- Trace of a product is invariant under simultaneous reindexing. -/
theorem trace_reindex_mul' {ι κ : Type} [Fintype ι] [Fintype κ] (e : ι ≃ κ) (A B : Op ι) :
    (Matrix.reindex e e A * Matrix.reindex e e B).trace = (A * B).trace := by
  rw [Matrix.reindex_apply, Matrix.reindex_apply, Matrix.submatrix_mul_equiv,
    trace_submatrix_equiv_eq]

/-- The output partial trace commutes with reindexing the input factor. -/
theorem ptraceOut_reindex_left {I I' O : Type} [Fintype O] (e : I ≃ I') (T : Op (I × O)) :
    ptraceOut (Matrix.reindex (e.prodCongr (Equiv.refl O)) (e.prodCongr (Equiv.refl O)) T)
      = Matrix.reindex e e (ptraceOut T) := by
  ext i j
  simp [ptraceOut_apply, Matrix.reindex_apply]

/-- A density operator stays a density operator under reindexing. -/
theorem Density.reindex {ι κ : Type} [Fintype ι] [Fintype κ] (e : ι ≃ κ) {σ : Op ι}
    (h : Density σ) : Density (Matrix.reindex e e σ) := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.reindex_apply]
    exact h.1.submatrix _
  · rw [Matrix.reindex_apply, trace_submatrix_equiv_eq]
    exact h.2

variable {I I' O X X' A A' : Type} [Fintype I] [Fintype I'] [Fintype O] [Fintype A] [Fintype A']
  [DecidableEq I] [DecidableEq I']

/-- Reindex an instrument along bijections of its input space, settings and outcomes. -/
def Instrument.reindex (eI : I ≃ I') (eX : X ≃ X') (eA : A ≃ A') (M : Instrument I O X A) :
    Instrument I' O X' A' where
  elem x a := Matrix.reindex (eI.prodCongr (Equiv.refl O)) (eI.prodCongr (Equiv.refl O))
    (M.elem (eX.symm x) (eA.symm a))
  positive x a := by
    rw [Matrix.reindex_apply]
    exact (M.positive _ _).submatrix _
  normalized x := by
    rw [← reindex_sum, Equiv.sum_comp eA.symm, ptraceOut_reindex_left, M.normalized,
      Matrix.reindex_apply, Matrix.submatrix_one_equiv]

@[simp] theorem Instrument.reindex_elem (eI : I ≃ I') (eX : X ≃ X') (eA : A ≃ A')
    (M : Instrument I O X A) (x : X') (a : A') :
    (M.reindex eI eX eA).elem x a
      = Matrix.reindex (eI.prodCongr (Equiv.refl O)) (eI.prodCongr (Equiv.refl O))
          (M.elem (eX.symm x) (eA.symm a)) := rfl

end Reindex

section Born

variable (D : Ports) {RA RB RA' RB' : Type}

/-- Reindexing the ancilla state reindexes the extended process along the induced regrouping
of the enlarged-input laboratory index. -/
theorem extendInput_reindex (eRA : RA ≃ RA') (eRB : RB ≃ RB') (W : PMat D) (σ : Op (RA × RB)) :
    extendInput D W (Matrix.reindex (eRA.prodCongr eRB) (eRA.prodCongr eRB) σ)
      = Matrix.reindex
          ((((Equiv.refl (Fin D.m)).prodCongr eRA).prodCongr (Equiv.refl (Fin D.d))).prodCongr
            (((Equiv.refl (Fin D.n)).prodCongr eRB).prodCongr (Equiv.refl (Fin D.e))))
          ((((Equiv.refl (Fin D.m)).prodCongr eRA).prodCongr (Equiv.refl (Fin D.d))).prodCongr
            (((Equiv.refl (Fin D.n)).prodCongr eRB).prodCongr (Equiv.refl (Fin D.e))))
          (extendInput D W σ) := by
  ext ⟨⟨⟨ai, ra⟩, ao⟩, ⟨⟨bi, rb⟩, bo⟩⟩ ⟨⟨⟨ai', ra'⟩, ao'⟩, ⟨⟨bi', rb'⟩, bo'⟩⟩
  simp [Matrix.reindex_apply, extendInput_eq_extended, extended_apply']

variable {X Y X' Y' A B A' B' : Type} [Fintype RA] [DecidableEq RA] [Fintype RB] [DecidableEq RB]
  [Fintype RA'] [DecidableEq RA'] [Fintype RB'] [DecidableEq RB'] [Fintype A] [Fintype B]
  [Fintype A'] [Fintype B']

/-- The extended Born distribution of reindexed data is the relabeled distribution
(`eq:born`; trace invariance under simultaneous reindexing). -/
theorem bornExtended_reindex (eRA : RA ≃ RA') (eRB : RB ≃ RB') (eX : X ≃ X') (eY : Y ≃ Y')
    (eA : A ≃ A') (eB : B ≃ B') (W : PMat D) (σ : Op (RA × RB))
    (M : Instrument (Fin D.m × RA) (Fin D.d) X A) (N : Instrument (Fin D.n × RB) (Fin D.e) Y B)
    (x : X') (y : Y') (a : A') (b : B') :
    bornExtended D W (Matrix.reindex (eRA.prodCongr eRB) (eRA.prodCongr eRB) σ)
        (M.reindex ((Equiv.refl (Fin D.m)).prodCongr eRA) eX eA)
        (N.reindex ((Equiv.refl (Fin D.n)).prodCongr eRB) eY eB) x y a b
      = bornExtended D W σ M N (eX.symm x) (eY.symm y) (eA.symm a) (eB.symm b) := by
  simp only [bornExtended, Instrument.reindex_elem, extendInput_reindex,
    Matrix.kroneckerMap_reindex, trace_reindex_mul']

end Born

/-! ### The general quantifier and the equivalence -/

/-- **Extensible causality over arbitrary finite data** (§2.2): `W` is valid and, for every pair
of finite ancilla types, every density operator on them, and every pair of extended instruments
with finite setting and outcome alphabets, the whole extended Born distribution is causal.
Only structurally necessary instances are assumed (see the module docstring). -/
def ExtensiblyCausalGen (D : Ports) (W : PMat D) : Prop :=
  Valid D W ∧
    ∀ (RA RB X Y A B : Type) [Fintype RA] [DecidableEq RA] [Fintype RB] [DecidableEq RB]
      [Fintype X] [Fintype Y] [Fintype A] [Fintype B] (σ : Op (RA × RB)), Density σ →
      ∀ (M : Instrument (Fin D.m × RA) (Fin D.d) X A)
        (N : Instrument (Fin D.n × RB) (Fin D.e) Y B),
        Causal (bornExtended D W σ M N)

/-- **The `Fin`-indexed and the general quantifiers agree**. -/
theorem extensiblyCausal_iff_gen (D : Ports) (W : PMat D) :
    ExtensiblyCausal D W ↔ ExtensiblyCausalGen D W := by
  constructor
  · rintro ⟨hW, h⟩
    refine ⟨hW, ?_⟩
    intro RA RB X Y A B _ _ _ _ _ _ _ _ σ hσ M N
    -- empty setting alphabets: causality is vacuous
    rcases isEmpty_or_nonempty X with hX | hX
    · exact causal_of_isEmpty_left _
    rcases isEmpty_or_nonempty Y with hY | hY
    · exact causal_of_isEmpty_right _
    -- empty ancillas contradict `Tr σ = 1`
    rcases isEmpty_or_nonempty RA with hRA | hRA
    · exfalso
      have h0 : σ.trace = 0 := by simp [Matrix.trace]
      exact zero_ne_one (h0.symm.trans hσ.2)
    rcases isEmpty_or_nonempty RB with hRB | hRB
    · exfalso
      have h0 : σ.trace = 0 := by simp [Matrix.trace]
      exact zero_ne_one (h0.symm.trans hσ.2)
    -- empty outcome alphabets contradict the normalization `Tr_O ∑ₐ M_{a|x} = I`
    rcases isEmpty_or_nonempty A with hA | hA
    · exfalso
      obtain ⟨x⟩ := hX
      have h0 : (0 : Op (Fin D.m × RA)) = 1 := by
        have := M.normalized x
        rwa [Finset.univ_eq_empty, Finset.sum_empty, ptraceOut_zero] at this
      obtain ⟨i⟩ : Nonempty (Fin D.m × RA) := inferInstance
      have := congrFun (congrFun h0 i) i
      simp at this
    rcases isEmpty_or_nonempty B with hB | hB
    · exfalso
      obtain ⟨y⟩ := hY
      have h0 : (0 : Op (Fin D.n × RB)) = 1 := by
        have := N.normalized y
        rwa [Finset.univ_eq_empty, Finset.sum_empty, ptraceOut_zero] at this
      obtain ⟨j⟩ : Nonempty (Fin D.n × RB) := inferInstance
      have := congrFun (congrFun h0 j) j
      simp at this
    -- everything nonempty: transport to `Fin` shapes
    obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero (Fintype.card_ne_zero (α := RA))
    obtain ⟨s, hs⟩ := Nat.exists_eq_succ_of_ne_zero (Fintype.card_ne_zero (α := RB))
    obtain ⟨nx, hnx⟩ := Nat.exists_eq_succ_of_ne_zero (Fintype.card_ne_zero (α := X))
    obtain ⟨ny, hny⟩ := Nat.exists_eq_succ_of_ne_zero (Fintype.card_ne_zero (α := Y))
    obtain ⟨na, hna⟩ := Nat.exists_eq_succ_of_ne_zero (Fintype.card_ne_zero (α := A))
    obtain ⟨nb, hnb⟩ := Nat.exists_eq_succ_of_ne_zero (Fintype.card_ne_zero (α := B))
    let eRA : RA ≃ Fin (r + 1) := Fintype.equivFinOfCardEq hr
    let eRB : RB ≃ Fin (s + 1) := Fintype.equivFinOfCardEq hs
    let eX : X ≃ Fin (nx + 1) := Fintype.equivFinOfCardEq hnx
    let eY : Y ≃ Fin (ny + 1) := Fintype.equivFinOfCardEq hny
    let eA : A ≃ Fin (na + 1) := Fintype.equivFinOfCardEq hna
    let eB : B ≃ Fin (nb + 1) := Fintype.equivFinOfCardEq hnb
    have hc := h r s nx ny na nb (Matrix.reindex (eRA.prodCongr eRB) (eRA.prodCongr eRB) σ)
      (Density.reindex _ hσ) (M.reindex ((Equiv.refl (Fin D.m)).prodCongr eRA) eX eA)
      (N.reindex ((Equiv.refl (Fin D.n)).prodCongr eRB) eY eB)
    refine Causal.of_relabel eX eY eA eB ?_
    convert hc using 1
    funext x y a b
    exact (bornExtended_reindex D eRA eRB eX eY eA eB W σ M N x y a b).symm
  · rintro ⟨hW, h⟩
    exact ⟨hW, fun r s nx ny na nb σ hσ M N => h _ _ _ _ _ _ σ hσ M N⟩

end CausalNonpurifiability
