module

public import Mathlib
public import CausalNonpurifiability.Linear.Indices
public import CausalNonpurifiability.Linear.PartialTrace

@[expose] public section


/-!
# `CausalNonpurifiability.Definitions.Purity`

Link contraction `eq:link` with partial transposition on the laboratory factors only,
channel/unitary Choi predicates, AFNB complete purity with arbitrary finite external systems,
the recovery map `reducePastFuture` (`eq:purification`), and `Purifiable`.

Manuscript anchors: `eq:link`, `eq:purification`, `eq:choi`, `eq:born`, AFNB Definitions 1
and 3 (§2.3, `sec:purity-definition`).

## Conventions

* A higher-order process `S : HigherOp D p f` lives on `(P × L) × F`: `P = Fin (p+1)` the
  global past, `L = LabIndex D` the laboratory factors in physical order `A_I, A_O, B_I, B_O`,
  `F = Fin (f+1)` the global future (successor dimensions: no empty spaces).
* The link layer uses ordinary **untransposed** Choi matrices `J` indexed by
  `(input, output)`: `J (i,o) (j,o') = ⟨o| 𝒜(|i⟩⟨j|) |o'⟩` (`eq:choi`, no dimension prefactor).
  Hence `ChannelChoi J := J.PosSemidef ∧ ptraceOut J = 1` (trace preservation `Tr_O J = I_I`)
  and a unitary channel `ρ ↦ U ρ U†` has `J (i,o) (j,o') = U o i * star (U o' j)`.
* External systems: the local channels act as `A_I ⊗ E_A → A_O ⊗ E'_A` and
  `B_I ⊗ E_B → B_O ⊗ E'_B` with `E_A = Fin (a+1)`, `E'_A = Fin (a'+1)`, `E_B = Fin (b+1)`,
  `E'_B = Fin (b'+1)`; all four sizes are universally quantified in `Deterministic` and `Pure`
  (AFNB extension convention: *completely* deterministic / pure; "pure" is **not** rank one).
* `link` implements `eq:link` entrywise; its docstring derives the index placement (the row
  laboratory index of `S` is paired with the row laboratory index of `J_A ⊗ J_B`, column with
  column — that is the effect of the partial transpose `T_L`).  `link_trivial` checks the
  formula against the Born rule `eq:born`.
* Recovery `eq:purification`: `W = Tr_F [⟨0|_P S |0⟩_P]`, literally
  `reducePastFuture S l l' = ∑ z, S ((0,l),z) ((0,l'),z)`.  The OQP-page formula differs by a
  full transpose on the remaining laboratory factors (manuscript §2.3, last paragraph);
  `reducePastFuture_transpose` records the elementary half of that compatibility
  (`reducePastFuture Sᵀ = (reducePastFuture S)ᵀ`); invariance of `Pure` under transposition
  (complex conjugation of the local unitaries) is `Pure.transpose` (`Boundary/Transpose.lean`),
  part of the endpoint `appendix_B`.

The theorems below are typing and sanity checks of the definitions, and two lemmas on
channels (`UnitaryChoi.channelChoi`, `ChannelChoi.prod`).
-/

set_option autoImplicit false

open Matrix
open scoped ComplexOrder Kronecker

noncomputable section

namespace CausalNonpurifiability

/-! ## Carrier types -/

/-- Higher-order Choi operator on `P ⊗ L ⊗ F` with global past `P = Fin (p+1)`, laboratory
factors `L = LabIndex D` (physical order `A_I, A_O, B_I, B_O`), and global future
`F = Fin (f+1)` (AFNB Definition 1; manuscript §2.3, `eq:link`). -/
abbrev HigherOp (D : Ports) (p f : ℕ) : Type :=
  Op ((Fin (p + 1) × LabIndex D) × Fin (f + 1))

/-- Untransposed Choi matrix (`eq:choi`) of a channel `A_I ⊗ E_A → A_O ⊗ E'_A` with external
systems `E_A = Fin (a+1)`, `E'_A = Fin (a'+1)`; index `((a_I, e_A), (a_O, e'_A))` in
`(input, output)` order (AFNB extension convention, §2.3). -/
abbrev ExtChoiA (D : Ports) (a a' : ℕ) : Type :=
  Op ((Fin D.m × Fin (a + 1)) × (Fin D.d × Fin (a' + 1)))

/-- Untransposed Choi matrix (`eq:choi`) of a channel `B_I ⊗ E_B → B_O ⊗ E'_B` with external
systems `E_B = Fin (b+1)`, `E'_B = Fin (b'+1)`; index `((b_I, e_B), (b_O, e'_B))`. -/
abbrev ExtChoiB (D : Ports) (b b' : ℕ) : Type :=
  Op ((Fin D.n × Fin (b + 1)) × (Fin D.e × Fin (b' + 1)))

/-- Input index of the linked channel `P ⊗ E_A ⊗ E_B → F ⊗ E'_A ⊗ E'_B` of `eq:link`: global
past and the two external inputs.  Reducible abbreviation of
`Fin (p+1) × (Fin (a+1) × Fin (b+1))`. -/
abbrev LinkIn (p a b : ℕ) : Type := Fin (p + 1) × (Fin (a + 1) × Fin (b + 1))

/-- Output index of the linked channel of `eq:link`: global future and the two external
outputs.  Reducible abbreviation of `Fin (f+1) × (Fin (a'+1) × Fin (b'+1))`. -/
abbrev LinkOut (f a' b' : ℕ) : Type := Fin (f + 1) × (Fin (a' + 1) × Fin (b' + 1))

/-! ## Channel and unitary Choi predicates -/

/-- `ChannelChoi J`: `J` is the untransposed Choi matrix (`eq:choi`, index `(input, output)`)
of a channel `I → O`: positive (complete positivity) and trace-preserving, `Tr_O J = I_I`
(the §2.1 normalization `Tr_{A_O} ∑ₐ M_{a|x} = I_{A_I}` for a single channel, stated in the
link-product layer without the Born-pairing transpose `M = Jᵀ`). -/
def ChannelChoi {I O : Type} [Fintype I] [Fintype O] [DecidableEq I] (J : Op (I × O)) : Prop :=
  J.PosSemidef ∧ ptraceOut J = 1

/-- `UnitaryChoi J`: `J` is the Choi matrix of a unitary channel `ρ ↦ U ρ U†`, i.e.
`J (i,o) (j,o') = U o i * star (U o' j)` (the unnormalized vectorization `|U⟩⟩⟨⟨U|`; `eq:choi`
carries no dimension prefactor) for some `U : Matrix O I ℂ` satisfying **both** unitary
equations `Uᴴ U = 1` and `U Uᴴ = 1` (AFNB Definition 3, "unitary channel"). -/
def UnitaryChoi {I O : Type} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]
    (J : Op (I × O)) : Prop :=
  ∃ U : Matrix O I ℂ,
    Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
    ∀ i o j o', J (i, o) (j, o') = U o i * star (U o' j)

/-! ## Link contraction (`eq:link`) -/

/-- `link D S JA JB = S * (J_A ⊗ J_B) = Tr_L [ S^{T_L} (J_A ⊗ J_B) ]` (`eq:link`): the Choi
matrix of the linked channel `P ⊗ E_A ⊗ E_B → F ⊗ E'_A ⊗ E'_B`, with the partial transpose on
the laboratory factors `L = A_I A_O B_I B_O` **only** and the contraction tracing out `L`.
Row index `u = ((p, (e_A, e_B)), (f, (e'_A, e'_B)))`, column index
`v = ((p', (e_A', e_B')), (f', (e'_A', e'_B')))`; `l = ((a_I, a_O), (b_I, b_O))` and `l'` range
over `LabIndex D`.

**Derivation of the entry formula.** Let `K := J_A ⊗ J_B`, regrouped on `L ⊗ E` with entries
`K (l, ε) (l', ε') = J_A ((a_I, e_A), (a_O, e'_A)) ((a_I', e_A'), (a_O', e'_A'))
· J_B ((b_I, e_B), (b_O, e'_B)) ((b_I', e_B'), (b_O', e'_B'))`, `ε = (e_A, e'_A, e_B, e'_B)`.
The partial transpose on `L` alone swaps only the laboratory indices of `S`:
`S^{T_L} ((p,l),f) ((p',l'),f') = S ((p,l'),f) ((p',l),f')`.  Multiplying (identities on the
unshared factors `P, F` resp. `E`) and tracing out `L` (equate the two surviving `L` indices
and sum) gives
```
(S * K) ((p,ε),(f,ε')) ((p',ε),(f',ε'))
  = ∑_{l₀ l₁} S^{T_L} ((p,l₀),f) ((p',l₁),f') · K (l₁,ε) (l₀,ε')
  = ∑_{l₀ l₁} S ((p,l₁),f) ((p',l₀),f') · K (l₁,ε) (l₀,ε')
  = ∑_{l l'}  S ((p,l),f) ((p',l'),f') · K (l,ε) (l',ε')        (l := l₁, l' := l₀).
```
So the **row** laboratory index of `S` is paired with the **row** laboratory index of
`J_A ⊗ J_B`, and column with column — exactly the effect of `T_L`; the transpose-free
contraction `Tr_L [S K]` would instead pair the row of `S` with the column of `K`
(`∑ S ((p,l'),f) ((p',l),f') · K (l,ε) (l',ε')`), which is **not** `eq:link`.
Sanity check (`link_trivial`): for trivial `P, F, E` the single entry is
`∑_{l l'} W l l' · K l l' = Tr[W Kᵀ] = Tr[W (M_A ⊗ M_B)]` with `M = Jᵀ` (`eq:choi`), the Born
rule `eq:born`; the row–row pairing is also why the link product is symmetric. -/
def link (D : Ports) {p f a a' b b' : ℕ}
    (S : HigherOp D p f) (JA : ExtChoiA D a a') (JB : ExtChoiB D b b') :
    Op (LinkIn p a b × LinkOut f a' b') :=
  Matrix.of fun u v =>
    ∑ l : LabIndex D, ∑ l' : LabIndex D,
      S ((u.1.1, l), u.2.1) ((v.1.1, l'), v.2.1) *
        JA ((l.1.1, u.1.2.1), (l.1.2, u.2.2.1)) ((l'.1.1, v.1.2.1), (l'.1.2, v.2.2.1)) *
        JB ((l.2.1, u.1.2.2), (l.2.2, u.2.2.2)) ((l'.2.1, v.1.2.2), (l'.2.2, v.2.2.2))

theorem link_apply (D : Ports) {p f a a' b b' : ℕ}
    (S : HigherOp D p f) (JA : ExtChoiA D a a') (JB : ExtChoiB D b b')
    (u v : LinkIn p a b × LinkOut f a' b') :
    link D S JA JB u v =
      ∑ l : LabIndex D, ∑ l' : LabIndex D,
        S ((u.1.1, l), u.2.1) ((v.1.1, l'), v.2.1) *
          JA ((l.1.1, u.1.2.1), (l.1.2, u.2.2.1)) ((l'.1.1, v.1.2.1), (l'.1.2, v.2.2.1)) *
          JB ((l.2.1, u.1.2.2), (l.2.2, u.2.2.2)) ((l'.2.1, v.1.2.2), (l'.2.2, v.2.2.2)) :=
  rfl

/-- `eq:link` entrywise with every index component named: row `((pI,(eA,eB)),(fO,(eA',eB')))`,
column `((pI',(eA₂,eB₂)),(fO',(eA₂',eB₂')))`. -/
theorem link_apply' (D : Ports) {p f a a' b b' : ℕ}
    (S : HigherOp D p f) (JA : ExtChoiA D a a') (JB : ExtChoiB D b b')
    (pI pI' : Fin (p + 1)) (fO fO' : Fin (f + 1)) (eA eA₂ : Fin (a + 1))
    (eA' eA₂' : Fin (a' + 1)) (eB eB₂ : Fin (b + 1)) (eB' eB₂' : Fin (b' + 1)) :
    link D S JA JB ((pI, (eA, eB)), (fO, (eA', eB'))) ((pI', (eA₂, eB₂)), (fO', (eA₂', eB₂'))) =
      ∑ l : LabIndex D, ∑ l' : LabIndex D,
        S ((pI, l), fO) ((pI', l'), fO') *
          JA ((l.1.1, eA), (l.1.2, eA')) ((l'.1.1, eA₂), (l'.1.2, eA₂')) *
          JB ((l.2.1, eB), (l.2.2, eB')) ((l'.2.1, eB₂), (l'.2.2, eB₂')) :=
  rfl

/-! ## Complete purity (AFNB Definitions 1 and 3) -/

/-- `Deterministic D S`: `S` is positive and, for **every** choice of finite external systems
and every pair of channels `A_I ⊗ E_A → A_O ⊗ E'_A`, `B_I ⊗ E_B → B_O ⊗ E'_B`, the link
contraction `eq:link` is again the Choi matrix of a channel `P E_A E_B → F E'_A E'_B`
(AFNB Definition 1 with its extension convention; manuscript §2.3). -/
def Deterministic (D : Ports) {p f : ℕ} (S : HigherOp D p f) : Prop :=
  S.PosSemidef ∧
  ∀ a a' b b' : ℕ,
  ∀ (JA : ExtChoiA D a a') (JB : ExtChoiB D b b'),
    ChannelChoi JA → ChannelChoi JB → ChannelChoi (link D S JA JB)

/-- `Pure D S`: `S` is deterministic and every pair of unitary channels, in the completely
extended sense (arbitrary finite external systems), is mapped by `eq:link` to a unitary channel
(AFNB Definition 3; "pure" does **not** mean rank one). -/
def Pure (D : Ports) {p f : ℕ} (S : HigherOp D p f) : Prop :=
  Deterministic D S ∧
  ∀ a a' b b' : ℕ,
  ∀ (JA : ExtChoiA D a a') (JB : ExtChoiB D b b'),
    UnitaryChoi JA → UnitaryChoi JB → UnitaryChoi (link D S JA JB)

theorem Pure.deterministic (D : Ports) {p f : ℕ} {S : HigherOp D p f} (h : Pure D S) :
    Deterministic D S :=
  h.1

theorem Deterministic.posSemidef (D : Ports) {p f : ℕ} {S : HigherOp D p f}
    (h : Deterministic D S) : S.PosSemidef :=
  h.1

/-! ## Recovery and purifiability (`eq:purification`) -/

/-- `reducePastFuture S = S * (|0⟩⟨0|_P ⊗ I_F) = Tr_F [ ⟨0|_P S |0⟩_P ]` (`eq:purification`),
literally `(l, l') ↦ ∑ z, S ((0,l),z) ((0,l'),z)`: input `|0⟩` on the global past, trace out
the global future. -/
def reducePastFuture (D : Ports) {p f : ℕ} (S : HigherOp D p f) : PMat D :=
  Matrix.of fun l l' => ∑ z : Fin (f + 1), S ((0, l), z) ((0, l'), z)

theorem reducePastFuture_apply (D : Ports) {p f : ℕ} (S : HigherOp D p f)
    (l l' : LabIndex D) :
    reducePastFuture D S l l' = ∑ z : Fin (f + 1), S ((0, l), z) ((0, l'), z) :=
  rfl

/-- `Purifiable D W`: there are finite past/future dimensions and a completely pure process `S`
on them whose recovery `eq:purification` is `W`.  Neither auxiliary dimension is prescribed
(manuscript §2.3). -/
def Purifiable (D : Ports) (W : PMat D) : Prop :=
  ∃ (p f : ℕ) (S : HigherOp D p f), Pure D S ∧ reducePastFuture D S = W

/-- Elementary half of the OQP-page transpose compatibility (manuscript §2.3, last paragraph):
recovering from the transposed higher-order process gives the transposed process matrix. -/
theorem reducePastFuture_transpose (D : Ports) {p f : ℕ} (S : HigherOp D p f) :
    reducePastFuture D Sᵀ = (reducePastFuture D S)ᵀ := by
  ext l l'
  simp only [reducePastFuture_apply, Matrix.transpose_apply]

/-! ## Sanity checks of the index conventions -/

/-- Trivial embedding of a process matrix as a higher-order process with one-dimensional past
and future: `S = |0⟩⟨0|_P ⊗ W ⊗ I_F` with `|P| = |F| = 1`, i.e. every entry is `W l l'`. -/
def trivialHigher (D : Ports) (W : PMat D) : HigherOp D 0 0 :=
  Matrix.of fun x y => W x.1.2 y.1.2

/-- A local Choi matrix on `A_I ⊗ A_O` regarded with one-dimensional external systems. -/
def trivialExtA (D : Ports) (J : Op (Fin D.m × Fin D.d)) : ExtChoiA D 0 0 :=
  Matrix.of fun x y => J (x.1.1, x.2.1) (y.1.1, y.2.1)

/-- A local Choi matrix on `B_I ⊗ B_O` regarded with one-dimensional external systems. -/
def trivialExtB (D : Ports) (J : Op (Fin D.n × Fin D.e)) : ExtChoiB D 0 0 :=
  Matrix.of fun x y => J (x.1.1, x.2.1) (y.1.1, y.2.1)

/-- Index-placement check for `link` (`eq:link` ⇒ `eq:born`): with trivial past, future and
external systems the (unique) entry of the link is `Tr[W (J_A ⊗ J_B)ᵀ] = Tr[W (M_A ⊗ M_B)]`,
the Born pairing `eq:born` in the `M = Jᵀ` convention of `eq:choi`. -/
theorem link_trivial (D : Ports) (W : PMat D) (JA : Op (Fin D.m × Fin D.d))
    (JB : Op (Fin D.n × Fin D.e)) (u v : LinkIn 0 0 0 × LinkOut 0 0 0) :
    link D (trivialHigher D W) (trivialExtA D JA) (trivialExtB D JB) u v =
      Matrix.trace (W * (JA ⊗ₖ JB)ᵀ) := by
  simp only [link_apply, trivialHigher, trivialExtA, trivialExtB, Matrix.of_apply, Matrix.trace,
    Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.kroneckerMap_apply,
    mul_assoc]

/-- Recovery inverts the trivial embedding (`eq:purification` with `|P| = |F| = 1`). -/
theorem reducePastFuture_trivialHigher (D : Ports) (W : PMat D) :
    reducePastFuture D (trivialHigher D W) = W := by
  ext l l'
  simp [reducePastFuture_apply, trivialHigher]

/-! ## Two lemmas on channels -/

/-- A unitary channel is a channel: `|U⟩⟩⟨⟨U|` is positive and `Tr_O |U⟩⟩⟨⟨U| = (Uᴴ U)ᵀ = I`. -/
theorem UnitaryChoi.channelChoi {I O : Type} [Fintype I] [Fintype O] [DecidableEq I]
    [DecidableEq O] {J : Op (I × O)} (h : UnitaryChoi J) : ChannelChoi J := by
  obtain ⟨U, hU1, -, hJ⟩ := h
  have hJeq : J = (Matrix.of fun (x : I × O) (_ : Unit) => U x.2 x.1) *
      (Matrix.of fun (x : I × O) (_ : Unit) => U x.2 x.1)ᴴ := by
    ext ⟨i, o⟩ ⟨j, o'⟩
    simp [Matrix.mul_apply, hJ]
  unfold ChannelChoi
  refine ⟨?_, ?_⟩
  · rw [hJeq]
    exact Matrix.posSemidef_self_mul_conjTranspose _
  · ext i j
    have h1 : (Uᴴ * U)ᵀ = 1 := by rw [hU1, Matrix.transpose_one]
    have h2 := congrFun (congrFun h1 i) j
    simp only [Matrix.transpose_apply, Matrix.mul_apply, Matrix.conjTranspose_apply] at h2
    rw [ptraceOut_apply, ← h2]
    exact Finset.sum_congr rfl fun o _ => by rw [hJ, mul_comm]

/-- Choi matrix of a product channel `𝒜 ⊗ ℬ`: `J_A ⊗ J_B` regrouped from
`(I_A × O_A) × (I_B × O_B)` to the `(input, output)` order `(I_A × I_B) × (O_A × O_B)`. -/
def prodChoi {IA OA IB OB : Type} (JA : Op (IA × OA)) (JB : Op (IB × OB)) :
    Op ((IA × IB) × (OA × OB)) :=
  Matrix.of fun x y => JA (x.1.1, x.2.1) (y.1.1, y.2.1) * JB (x.1.2, x.2.2) (y.1.2, y.2.2)

theorem prodChoi_eq_submatrix {IA OA IB OB : Type} (JA : Op (IA × OA)) (JB : Op (IB × OB)) :
    prodChoi JA JB =
      (JA ⊗ₖ JB).submatrix (Equiv.prodProdProdComm IA IB OA OB)
        (Equiv.prodProdProdComm IA IB OA OB) := by
  ext x y
  rfl

/-- The Choi matrix of a product of channels is the Choi matrix of a channel. -/
theorem ChannelChoi.prod {IA OA IB OB : Type} [Fintype IA] [Fintype OA] [Fintype IB]
    [Fintype OB] [DecidableEq IA] [DecidableEq IB] {JA : Op (IA × OA)} {JB : Op (IB × OB)}
    (hA : ChannelChoi JA) (hB : ChannelChoi JB) : ChannelChoi (prodChoi JA JB) := by
  unfold ChannelChoi
  refine ⟨?_, ?_⟩
  · rw [prodChoi_eq_submatrix]
    exact (hA.1.kronecker hB.1).submatrix _
  · ext x y
    have hA2 := congrFun (congrFun hA.2 x.1) y.1
    have hB2 := congrFun (congrFun hB.2 x.2) y.2
    rw [ptraceOut_apply] at hA2 hB2
    rw [← Matrix.one_kronecker_one]
    simp only [Matrix.kroneckerMap_apply, ← hA2, ← hB2, Finset.sum_mul, Finset.mul_sum,
      ptraceOut_apply, prodChoi, Matrix.of_apply, Fintype.sum_prod_type]
    rw [Finset.sum_comm]

end CausalNonpurifiability

end
