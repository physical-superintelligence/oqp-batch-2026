module

public import CausalNonpurifiability.Definitions.ProcessSwapCore
public import CausalNonpurifiability.Definitions.Purity
public import CausalNonpurifiability.Definitions.Process
public import CausalNonpurifiability.Linear.Unitary

@[expose] public section


/-!
# `CausalNonpurifiability.Boundary.Swap`

The party swap `A ↔ B` as a symmetry of every predicate of the development (the companion of
the transposition module `Boundary/Transpose`): `Ports.swap D = (n, e, m, d)`, `swapP W` (exchange the two
laboratory factor pairs), `swapH S` (the same exchange inside the laboratory factor of a
higher-order operator, past and future fixed).  Replacement maps, `L_V`, validity, the two
ordered cones, causal separability, the link contraction `eq:link` (with the two external systems
exchanged), channel/unitary Choi predicates, determinism, complete purity, the recovery
`eq:purification` and purifiability are all transported.  Main consumer: manuscript §9, the end
of the proof of Proposition 9.2 ("For a process in `O_{B≺A}` we exchange the two parties") —
`orderedBA_purifiable hW hV := Purifiable.swap D (orderedAB_purifiable (Valid.swap D hW)
(OrderedBA.swap D hV))`.

Conventions: `Ports.swap` is reducible, so `D.swap.m` unfolds to `D.n` etc.; in particular
`ExtChoiA D.swap a a'` and `ExtChoiB D a a'` are the *same* type, so no reindexing of the local
Choi data is needed — a Bob channel of `D` is literally an Alice channel of `D.swap`.  On the
linked channel the exchange of the external systems is `swapLink`
(`((p,(e_A,e_B)),(f,(e'_A,e'_B))) ↦ ((p,(e_B,e_A)),(f,(e'_B,e'_A)))`).

Manuscript anchors: `eq:replacement`, `eq:LV`, `eq:valid`, `eq:ordered-cones`, `eq:link`,
`eq:purification`, §9 (Proposition 9.2).
-/

set_option autoImplicit false

open scoped Kronecker ComplexOrder Matrix

namespace CausalNonpurifiability

noncomputable section

/-! ### The party swap on ports and indices -/

@[simp] theorem Ports.swap_m (D : Ports) : D.swap.m = D.n := rfl
@[simp] theorem Ports.swap_d (D : Ports) : D.swap.d = D.e := rfl
@[simp] theorem Ports.swap_n (D : Ports) : D.swap.n = D.m := rfl
@[simp] theorem Ports.swap_e (D : Ports) : D.swap.e = D.d := rfl

/-- The swap is an involution (definitionally, by structure eta). -/
theorem Ports.swap_swap (D : Ports) : D.swap.swap = D := rfl

section Swap

variable (D : Ports)


@[simp] theorem swapLab_apply (x : LabIndex D) : swapLab D x = (x.2, x.1) := rfl
@[simp] theorem swapLab_symm_apply (y : LabIndex D.swap) : (swapLab D).symm y = (y.2, y.1) := rfl


theorem swapP_apply (W : PMat D) (x y : LabIndex D.swap) :
    swapP D W x y = W (x.2, x.1) (y.2, y.1) := rfl

theorem swapP_add (W W' : PMat D) : swapP D (W + W') = swapP D W + swapP D W' := by
  ext x y; rfl

theorem swapP_sub (W W' : PMat D) : swapP D (W - W') = swapP D W - swapP D W' := by
  ext x y; rfl

theorem swapP_smul (c : ℂ) (W : PMat D) : swapP D (c • W) = c • swapP D W := by
  ext x y; rfl

theorem swapP_zero : swapP D (0 : PMat D) = 0 := by
  ext x y; rfl

/-- Swapping twice is the identity (`D.swap.swap = D` definitionally). -/
theorem swapP_swapP (W : PMat D) : swapP D.swap (swapP D W) = W := by
  ext ⟨⟨_, _⟩, ⟨_, _⟩⟩ ⟨⟨_, _⟩, ⟨_, _⟩⟩; rfl

theorem swapP_isHermitian {W : PMat D} (h : W.IsHermitian) : (swapP D W).IsHermitian := by
  unfold swapP
  rw [Matrix.reindex_apply]
  exact h.submatrix _

theorem swapP_posSemidef {W : PMat D} (h : W.PosSemidef) : (swapP D W).PosSemidef := by
  unfold swapP
  rw [Matrix.reindex_apply]
  exact h.submatrix _

theorem trace_swapP (W : PMat D) : (swapP D W).trace = W.trace := by
  unfold swapP
  rw [Matrix.reindex_apply, trace_submatrix_equiv']

/-! ### Replacement maps commute with the swap (`eq:replacement`) -/

theorem R_AO_swapP (W : PMat D) : R_AO (swapP D W) = swapP D (R_BO W) := by
  ext ⟨⟨b, t⟩, ⟨a, o⟩⟩ ⟨⟨b', t'⟩, ⟨a', o'⟩⟩
  simp only [R_AO_apply, R_BO_apply, swapP_apply]

theorem R_BO_swapP (W : PMat D) : R_BO (swapP D W) = swapP D (R_AO W) := by
  ext ⟨⟨b, t⟩, ⟨a, o⟩⟩ ⟨⟨b', t'⟩, ⟨a', o'⟩⟩
  simp only [R_AO_apply, R_BO_apply, swapP_apply]

theorem R_AIAO_swapP (W : PMat D) : R_AIAO (swapP D W) = swapP D (R_BIBO W) := by
  ext ⟨⟨b, t⟩, ⟨a, o⟩⟩ ⟨⟨b', t'⟩, ⟨a', o'⟩⟩
  simp only [R_AIAO_apply, R_BIBO_apply, swapP_apply]

theorem R_BIBO_swapP (W : PMat D) : R_BIBO (swapP D W) = swapP D (R_AIAO W) := by
  ext ⟨⟨b, t⟩, ⟨a, o⟩⟩ ⟨⟨b', t'⟩, ⟨a', o'⟩⟩
  simp only [R_AIAO_apply, R_BIBO_apply, swapP_apply]

/-! ### Process predicates -/

/-- `L_V` is swap-invariant (`eq:LV-a` and `eq:LV-b` are exchanged, `eq:LV-c` is symmetric). -/
theorem GenLV.swap {W : PMat D} (h : GenLV W) : GenLV (swapP D W) := by
  obtain ⟨hH, ha, hb, hc⟩ := h
  refine ⟨swapP_isHermitian D hH, ?_, ?_, ?_⟩
  · rw [R_BIBO_swapP, R_AO_swapP, ← swapP_sub, hb, swapP_zero]
  · rw [R_AIAO_swapP, R_BO_swapP, ← swapP_sub, ha, swapP_zero]
  · rw [R_AO_swapP, R_BO_swapP, R_AO_swapP, ← swapP_sub, ← swapP_sub, ← swapP_add,
      ← R_AO_R_BO_comm, sub_right_comm, hc, swapP_zero]

theorem InLV.swap {W : PMat D} (h : InLV D W) : InLV D.swap (swapP D W) := GenLV.swap D h

/-- Validity is swap-invariant (`eq:valid`; `Tr W = de = ed`). -/
theorem Valid.swap {W : PMat D} (h : Valid D W) : Valid D.swap (swapP D W) :=
  ⟨InLV.swap D h.1, swapP_posSemidef D h.2.1, by
    rw [trace_swapP, h.2.2]
    exact congrArg (Nat.cast : ℕ → ℂ) (Nat.mul_comm D.d D.e)⟩

/-- `O_{B≺A}` of `D` is `O_{A≺B}` of `D.swap` (`eq:ordered-cones`). -/
theorem OrderedBA.swap {W : PMat D} (h : OrderedBA D W) : OrderedAB D.swap (swapP D W) :=
  ⟨InLV.swap D h.1, swapP_posSemidef D h.2.1, by rw [R_BO_swapP, h.2.2]⟩

/-- `O_{A≺B}` of `D` is `O_{B≺A}` of `D.swap` (`eq:ordered-cones`). -/
theorem OrderedAB.swap {W : PMat D} (h : OrderedAB D W) : OrderedBA D.swap (swapP D W) :=
  ⟨InLV.swap D h.1, swapP_posSemidef D h.2.1, by rw [R_AO_swapP, h.2.2]⟩

theorem CausallySeparable.swap {W : PMat D} (h : CausallySeparable D W) :
    CausallySeparable D.swap (swapP D W) := by
  obtain ⟨hV, U, V, hU, hV', rfl⟩ := h
  exact ⟨Valid.swap D hV, swapP D V, swapP D U, OrderedBA.swap D hV', OrderedAB.swap D hU, by
    rw [swapP_add, add_comm]⟩

/-! ### Higher-order operators and the link (`eq:link`) -/

/-- The swap inside the laboratory factor of `(P × L) × F`, past and future fixed. -/
def swapHigh (p f : ℕ) :
    (Fin (p + 1) × LabIndex D) × Fin (f + 1) ≃ (Fin (p + 1) × LabIndex D.swap) × Fin (f + 1) where
  toFun x := ((x.1.1, swapLab D x.1.2), x.2)
  invFun y := ((y.1.1, (swapLab D).symm y.1.2), y.2)
  left_inv := fun ⟨⟨_, ⟨_, _⟩⟩, _⟩ => rfl
  right_inv := fun ⟨⟨_, ⟨_, _⟩⟩, _⟩ => rfl

@[simp] theorem swapHigh_apply (p f : ℕ) (x : (Fin (p + 1) × LabIndex D) × Fin (f + 1)) :
    swapHigh D p f x = ((x.1.1, (x.1.2.2, x.1.2.1)), x.2) := rfl

@[simp] theorem swapHigh_symm_apply (p f : ℕ) (y : (Fin (p + 1) × LabIndex D.swap) × Fin (f + 1)) :
    (swapHigh D p f).symm y = ((y.1.1, (y.1.2.2, y.1.2.1)), y.2) := rfl

/-- The swapped higher-order operator. -/
def swapH {p f : ℕ} (S : HigherOp D p f) : HigherOp D.swap p f :=
  Matrix.reindex (swapHigh D p f) (swapHigh D p f) S

theorem swapH_apply {p f : ℕ} (S : HigherOp D p f)
    (x y : (Fin (p + 1) × LabIndex D.swap) × Fin (f + 1)) :
    swapH D S x y = S ((x.1.1, (x.1.2.2, x.1.2.1)), x.2) ((y.1.1, (y.1.2.2, y.1.2.1)), y.2) := rfl

theorem swapH_swapH {p f : ℕ} (S : HigherOp D p f) : swapH D.swap (swapH D S) = S := by
  ext ⟨⟨_, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, _⟩ ⟨⟨_, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, _⟩; rfl

theorem swapH_posSemidef {p f : ℕ} {S : HigherOp D p f} (h : S.PosSemidef) :
    (swapH D S).PosSemidef := by
  unfold swapH
  rw [Matrix.reindex_apply]
  exact h.submatrix _

/-- Exchange of the two external inputs (resp. outputs) of the linked channel. -/
def swapIn (p a b : ℕ) : LinkIn p a b ≃ LinkIn p b a where
  toFun u := (u.1, (u.2.2, u.2.1))
  invFun u := (u.1, (u.2.2, u.2.1))
  left_inv := fun ⟨_, ⟨_, _⟩⟩ => rfl
  right_inv := fun ⟨_, ⟨_, _⟩⟩ => rfl

/-- Exchange of the two external inputs and of the two external outputs of the linked channel:
`((p,(e_A,e_B)),(f,(e'_A,e'_B))) ↦ ((p,(e_B,e_A)),(f,(e'_B,e'_A)))`. -/
def swapLink (p f a a' b b' : ℕ) :
    LinkIn p a b × LinkOut f a' b' ≃ LinkIn p b a × LinkOut f b' a' :=
  (swapIn p a b).prodCongr (swapIn f a' b')

theorem swapLink_symm_apply (p f a a' b b' : ℕ) (u : LinkIn p b a) (w : LinkOut f b' a') :
    (swapLink p f a a' b b').symm (u, w) = ((swapIn p a b).symm u, (swapIn f a' b').symm w) := rfl

theorem swapLink_symm_apply' (p f a a' b b' : ℕ) (u : LinkIn p b a × LinkOut f b' a') :
    (swapLink p f a a' b b').symm u
      = ((u.1.1, (u.1.2.2, u.1.2.1)), (u.2.1, (u.2.2.2, u.2.2.1))) := rfl

/-- **The link of swapped data** (`eq:link`): a Bob channel of `D` is an Alice channel of
`D.swap`, and the linked channel is the original one with the external systems exchanged. -/
theorem link_swap {p f a a' b b' : ℕ} (S : HigherOp D p f) (JA : ExtChoiA D a a')
    (JB : ExtChoiB D b b') :
    link D.swap (swapH D S) JB JA
      = Matrix.reindex (swapLink p f a a' b b') (swapLink p f a a' b b') (link D S JA JB) := by
  ext u v
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, link_apply, link_apply]
  refine Fintype.sum_equiv (swapLab D).symm _ _ fun m => ?_
  refine Fintype.sum_equiv (swapLab D).symm _ _ fun m' => ?_
  simp only [swapH_apply, swapLab_symm_apply, swapLink_symm_apply']
  ring

/-! ### Choi predicates are transported along `swapLink` -/

section ChoiSwap

variable {p f a a' b b' : ℕ}

theorem ptraceOut_reindex_swapLink (J : Op (LinkIn p a b × LinkOut f a' b')) :
    ptraceOut (Matrix.reindex (swapLink p f a a' b b') (swapLink p f a a' b b') J)
      = Matrix.reindex (swapIn p a b) (swapIn p a b) (ptraceOut J) := by
  ext u u'
  simp only [ptraceOut_apply, Matrix.reindex_apply, Matrix.submatrix_apply, swapLink_symm_apply]
  exact Equiv.sum_comp (swapIn f a' b').symm
    (fun w => J ((swapIn p a b).symm u, w) ((swapIn p a b).symm u', w))

theorem ChannelChoi.reindex_swapLink {J : Op (LinkIn p a b × LinkOut f a' b')}
    (h : ChannelChoi J) :
    ChannelChoi (Matrix.reindex (swapLink p f a a' b b') (swapLink p f a a' b b') J) := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.reindex_apply]
    exact h.1.submatrix _
  · rw [ptraceOut_reindex_swapLink, h.2, Matrix.reindex_apply, Matrix.submatrix_one_equiv]

theorem UnitaryChoi.reindex_swapLink {J : Op (LinkIn p a b × LinkOut f a' b')}
    (h : UnitaryChoi J) :
    UnitaryChoi (Matrix.reindex (swapLink p f a a' b b') (swapLink p f a a' b b') J) := by
  obtain ⟨U, hU1, hU2, hJ⟩ := h
  refine ⟨Matrix.reindex (swapIn f a' b') (swapIn p a b) U,
    conjTranspose_mul_self_reindex _ _ hU1, self_mul_conjTranspose_reindex _ _ hU2, ?_⟩
  intro i o j o'
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, swapLink_symm_apply]
  exact hJ _ _ _ _

end ChoiSwap

/-! ### Determinism, complete purity, recovery, purifiability -/

/-- Determinism is swap-invariant (AFNB Def. 1 through `link_swap`). -/
theorem Deterministic.swap {p f : ℕ} {S : HigherOp D p f} (h : Deterministic D S) :
    Deterministic D.swap (swapH D S) := by
  refine ⟨swapH_posSemidef D h.1, ?_⟩
  intro a a' b b' JA' JB' hA hB
  rw [link_swap D S JB' JA']
  exact ChannelChoi.reindex_swapLink (h.2 b b' a a' JB' JA' hB hA)

/-- Complete purity is swap-invariant (AFNB Def. 3 through `link_swap`). -/
theorem Pure.swap {p f : ℕ} {S : HigherOp D p f} (h : Pure D S) : Pure D.swap (swapH D S) := by
  refine ⟨Deterministic.swap D h.1, ?_⟩
  intro a a' b b' JA' JB' hA hB
  rw [link_swap D S JB' JA']
  exact UnitaryChoi.reindex_swapLink (h.2 b b' a a' JB' JA' hB hA)

/-- Recovery `eq:purification` commutes with the swap. -/
theorem reducePastFuture_swap {p f : ℕ} (S : HigherOp D p f) :
    reducePastFuture D.swap (swapH D S) = swapP D (reducePastFuture D S) := by
  ext l l'
  simp only [reducePastFuture_apply, swapP_apply, swapH_apply]

/-- Purifiability transports to the swapped process. -/
theorem Purifiable.swap' {W : PMat D} (h : Purifiable D W) : Purifiable D.swap (swapP D W) := by
  obtain ⟨p, f, S, hS, hred⟩ := h
  exact ⟨p, f, swapH D S, Pure.swap D hS, by rw [reducePastFuture_swap, hred]⟩

/-- **Purifiability of the swapped process gives purifiability** (manuscript §9: "For a
process in `O_{B≺A}` we exchange the two parties"). -/
theorem Purifiable.swap {W : PMat D} (h : Purifiable D.swap (swapP D W)) : Purifiable D W := by
  obtain ⟨p, f, S', hS', hred⟩ := h
  have h1 := reducePastFuture_swap D.swap S'
  rw [hred, swapP_swapP] at h1
  exact ⟨p, f, swapH D.swap S', Pure.swap D.swap hS', h1⟩

theorem purifiable_swap_iff (W : PMat D) : Purifiable D.swap (swapP D W) ↔ Purifiable D W :=
  ⟨Purifiable.swap D, Purifiable.swap' D⟩

end Swap

end

end CausalNonpurifiability
