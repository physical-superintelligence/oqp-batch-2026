module

public import Mathlib

/-!
# Statement of record: `2(d-1)` PPT maps compose to an entanglement-breaking map

This is the file a reader audits. It imports only Mathlib. The definitions in the first part are
copied verbatim (same names and bodies) from `PPTCompositionBound/Defs.lean`, together with the
three small lemmas that the definition of `refMap` uses. Each theorem in the second part ends in
`sorry`; `Solution.lean` proves the same statements from the library, and Comparator checks that
the two agree and that the proofs use only the axioms `propext`, `Quot.sound` and
`Classical.choice`.

## The result

For `d ≥ 2`, the composition of any `2(d-1)` PPT maps on `d × d` complex matrices is
entanglement breaking (`compose_ppt_maps_entanglementBreaking`, Theorem 1 of the paper). The
maps may all be different, trace preserving or not. For a single map this says that the
entanglement-breaking index of a PPT map on `M_d` is at most `2(d-1)` (`ebIndex_le_of_isPPTMap`).

## Relation to Open Quantum Problem 38

Problem 38 of the Open Quantum Problems list, "The PPT-squared conjecture", asks whether
entanglement swapping of two states with positive partial transpose always gives a separable state:
"The conjecture [1] by Matthias Christandl states that all such σ_AD are separable. Of course, the
problem is to prove or disprove this." (LaTeX rendered as plain text.) In map form (Christandl,
Müller-Hermes and Wolf, 2019) the conjecture says that the composition of any two PPT maps is
entanglement breaking. It is false: an OpenAI preprint of 27 September 2026 gives two PPT maps on
`10 × 10` matrices whose composition is not entanglement breaking, and a trace-preserving PPT
channel on `21 × 21` matrices whose square is not. The theorems below prove the bound with `2(d-1)`
maps in place of two, a number that depends on the dimension, for all PPT maps on `M_d`. The full
entry is quoted in
`docs/OQP_STATEMENT.md`; `docs/FIDELITY.md` maps its wording to the definitions here.

## Conventions

* `M_d` is `Matrix (Fin d) (Fin d) ℂ`; a map is a `ℂ`-linear map between matrix algebras.
* An operator on `ℂ^κ ⊗ ℂ^n` is a `Matrix (κ × n) (κ × n) ℂ`. The first factor `κ` is the
  reference system; the second factor is the system on which the maps act.
* "Positive" means `Matrix.PosSemidef`. Operators are unnormalized, and maps are arbitrary linear
  maps (trace preserving or not).
* A PPT map is a map that is completely positive and completely copositive.
-/

@[expose] public section

/-! ## Definitions, verbatim from `PPTCompositionBound/Defs.lean` -/

open Matrix
open scoped Kronecker ComplexOrder

namespace PPTCompositionBound

variable {n p : Type*}

/-- The `(i, j)` block of an operator on `ℂ^κ ⊗ ℂ^n` with respect to the reference basis. -/
def block {κ : Type*} (X : Matrix (κ × n) (κ × n) ℂ) (i j : κ) : Matrix n n ℂ :=
  Matrix.of fun a b => X (i, a) (j, b)

@[simp]
theorem block_apply {κ : Type*} (X : Matrix (κ × n) (κ × n) ℂ) (i j : κ) (a b : n) :
    block X i j a b = X (i, a) (j, b) :=
  rfl

theorem block_add {κ : Type*} (X Y : Matrix (κ × n) (κ × n) ℂ) (i j : κ) :
    block (X + Y) i j = block X i j + block Y i j := by
  ext a b
  simp

theorem block_smul {κ : Type*} (c : ℂ) (X : Matrix (κ × n) (κ × n) ℂ) (i j : κ) :
    block (c • X) i j = c • block X i j := by
  ext a b
  simp

/-- The map `id_κ ⊗ Φ` on `M_κ ⊗ M_n`: it applies `Φ` to every block,
`((id ⊗ Φ) X)_{(i,a),(j,b)} = Φ(X_{ij})_{ab}` where `X_{ij}` is the `(i, j)` block of `X`. -/
def refMap (κ : Type*) (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ) :
    Matrix (κ × n) (κ × n) ℂ →ₗ[ℂ] Matrix (κ × p) (κ × p) ℂ where
  toFun X := Matrix.of fun x y => Φ (block X x.1 y.1) x.2 y.2
  map_add' X Y := by
    ext x y
    simp [block_add]
  map_smul' c X := by
    ext x y
    simp [block_smul]

/-- Matrix transposition `t(N) = Nᵀ` as a complex-linear map. -/
def transposeMap (p : Type*) : Matrix p p ℂ →ₗ[ℂ] Matrix p p ℂ :=
  (Matrix.transposeLinearEquiv p p ℂ ℂ).toLinearMap

/-! ### Completely positive, completely copositive and PPT maps -/

/-- `Φ` is completely positive: `id_k ⊗ Φ` maps positive operators to positive operators for
every reference dimension `k`. -/
def IsCompletelyPositive (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ) : Prop :=
  ∀ (k : ℕ) (X : Matrix (Fin k × n) (Fin k × n) ℂ), X.PosSemidef →
    (refMap (Fin k) Φ X).PosSemidef

/-- `Φ` is completely copositive: `t ∘ Φ` is completely positive, where `t` is transposition on
the output algebra. -/
def IsCompletelyCopositive (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ) : Prop :=
  IsCompletelyPositive (transposeMap p ∘ₗ Φ)

/-- A PPT map is a linear map that is both completely positive and completely copositive.
No trace-preservation is assumed. -/
def IsPPTMap (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ) : Prop :=
  IsCompletelyPositive Φ ∧ IsCompletelyCopositive Φ

/-! ### Separability and entanglement breaking -/

/-- A bipartite operator is separable if it is a finite sum of tensor products of positive
operators. No normalization is imposed; the empty sum shows that `0` is separable. -/
def IsSeparable {κ : Type*} (X : Matrix (κ × n) (κ × n) ℂ) : Prop :=
  ∃ (N : ℕ) (A : Fin N → Matrix κ κ ℂ) (B : Fin N → Matrix n n ℂ),
    (∀ i, (A i).PosSemidef) ∧ (∀ i, (B i).PosSemidef) ∧ X = ∑ i, A i ⊗ₖ B i

/-- A completely positive map is entanglement breaking if `(id_k ⊗ Φ)(X)` is separable for every
reference dimension `k` and every positive bipartite input `X` (not necessarily normalized). -/
def IsEntanglementBreaking (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ) : Prop :=
  IsCompletelyPositive Φ ∧
    ∀ (k : ℕ) (X : Matrix (Fin k × n) (Fin k × n) ℂ), X.PosSemidef →
      IsSeparable (refMap (Fin k) Φ X)

/-- The ordered composition `Φ_N ∘ ⋯ ∘ Φ_1` of a list `[Φ_1, …, Φ_N]` of endomorphisms; the head
of the list is applied first, and the empty composition is the identity. -/
def compList (L : List (Module.End ℂ (Matrix n n ℂ))) : Module.End ℂ (Matrix n n ℂ) :=
  L.foldl (fun acc φ => φ ∘ₗ acc) LinearMap.id

/-- The entanglement-breaking index `n(T) = min {m ≥ 1 : T^m is entanglement breaking}`, with
value `⊤` when no positive power of `T` is entanglement breaking. -/
noncomputable def ebIndex (T : Module.End ℂ (Matrix n n ℂ)) : ℕ∞ :=
  ⨅ (m : ℕ) (_ : 1 ≤ m) (_ : IsEntanglementBreaking (T ^ m)), (m : ℕ∞)

/-- Partial transposition `X ↦ X^{Γ_R}` on the reference factor: it swaps the block indices
without transposing the blocks themselves. -/
def partialTransposeRef {κ : Type*} (X : Matrix (κ × n) (κ × n) ℂ) : Matrix (κ × n) (κ × n) ℂ :=
  Matrix.of fun x y => X (y.1, x.2) (x.1, y.2)

/-- The (unnormalized) pure operator `P_v = |v⟩⟨v|`. -/
def pureState {ι : Type*} (v : ι → ℂ) : Matrix ι ι ℂ :=
  Matrix.vecMulVec v (star v)

/-! ## Main results -/

/-- **Theorem 1 of the paper (headline).** Let `d ≥ 2` and let `Φ_1, …, Φ_{2(d-1)}` be PPT maps on
`M_d`, possibly all different, trace preserving or not. Then the composition
`Φ_{2(d-1)} ∘ ⋯ ∘ Φ_1` is entanglement breaking. (Lean counts from `0`: `Φ_i` is `Φ (i - 1)`, and
`compList` applies the head of the list first, so `Φ 0 = Φ_1` acts first.) -/
theorem compose_ppt_maps_entanglementBreaking (d : ℕ) (hd : 2 ≤ d)
    (Φ : Fin (2 * (d - 1)) → Module.End ℂ (Matrix (Fin d) (Fin d) ℂ))
    (hΦ : ∀ i, IsPPTMap (Φ i)) :
    IsEntanglementBreaking (compList (List.ofFn Φ)) := by
  sorry

/-- **Theorem 1, second sentence.** For `d ≥ 2`, the entanglement-breaking index of a PPT map `T`
on `M_d` (the least `m ≥ 1` such that `T^m` is entanglement breaking) is at most `2(d-1)`. -/
theorem ebIndex_le_of_isPPTMap (d : ℕ) (hd : 2 ≤ d) (T : Module.End ℂ (Matrix (Fin d) (Fin d) ℂ))
    (hT : IsPPTMap T) : ebIndex T ≤ ((2 * (d - 1) : ℕ) : ℕ∞) := by
  sorry

/-- **More maps.** For `d ≥ 2` and any `N ≥ 2(d-1)`, the composition of `N` PPT maps on `M_d` is
entanglement breaking. (It follows because following an entanglement-breaking map by a completely
positive map keeps it entanglement breaking.) -/
theorem compose_at_least_ppt_maps_entanglementBreaking (d : ℕ) (hd : 2 ≤ d) (N : ℕ)
    (hN : 2 * (d - 1) ≤ N) (Φ : Fin N → Module.End ℂ (Matrix (Fin d) (Fin d) ℂ))
    (hΦ : ∀ i, IsPPTMap (Φ i)) :
    IsEntanglementBreaking (compList (List.ofFn Φ)) := by
  sorry

/-- **Interleaved form.** The entanglement-breaking index as defined by Lami and Giovannetti
(2015), and recalled by Christandl, Müller-Hermes and Wolf (2019), allows arbitrary channels between
the copies of `T`; `ebIndex` above is the paper's power index. For `d ≥ 2`, a PPT map `T` on `M_d`
and completely positive maps `S_1, …, S_{2d-3}` on `M_d` (trace preserving or not), the
composition `T ∘ S_{2d-3} ∘ T ∘ ⋯ ∘ T ∘ S_1 ∘ T`, with `2(d-1)` copies of `T`, is entanglement
breaking. (Lean counts from `0`: `S_i` is `S (i - 1)`.) -/
theorem compose_ppt_map_interleaved_entanglementBreaking (d : ℕ) (hd : 2 ≤ d)
    (T : Module.End ℂ (Matrix (Fin d) (Fin d) ℂ)) (hT : IsPPTMap T)
    (S : Fin (2 * (d - 1) - 1) → Module.End ℂ (Matrix (Fin d) (Fin d) ℂ))
    (hS : ∀ i, IsCompletelyPositive (S i)) :
    IsEntanglementBreaking (compList (T :: List.ofFn fun i => T ∘ₗ S i)) := by
  sorry

/-! ## Sanity checks on the definitions

These guard against vacuous or nonstandard definitions: entanglement exists in this model, the
identity map is not entanglement breaking, complete positivity, the PPT property and entanglement
breaking agree with the standard Choi-matrix criteria, complete copositivity does not imply complete
positivity, and the conventions of `compList` and `ebIndex` are as described. -/

/-- Separability is a real restriction: for `d ≥ 2` some positive operator on `ℂ² ⊗ ℂ^d` is not
separable. -/
theorem exists_posSemidef_not_isSeparable (d : ℕ) (hd : 2 ≤ d) :
    ∃ X : Matrix (Fin 2 × Fin d) (Fin 2 × Fin d) ℂ,
      X.PosSemidef ∧ ¬ PPTCompositionBound.IsSeparable X := by
  sorry

/-- The conclusion of Theorem 1 is not automatic: for `d ≥ 2` the identity map on `M_d` (a
composition of zero PPT maps) is not entanglement breaking. -/
theorem id_not_entanglementBreaking (d : ℕ) (hd : 2 ≤ d) :
    ¬ IsEntanglementBreaking (LinearMap.id : Module.End ℂ (Matrix (Fin d) (Fin d) ℂ)) := by
  sorry

/-- Choi's theorem for this definition: `Φ : M_d → M_p` is completely positive iff its Choi matrix
`(id_d ⊗ Φ)(|Ω⟩⟨Ω|)`, with `Ω = ∑_i e_i ⊗ e_i`, is positive. -/
theorem choi_isCompletelyPositive_iff {d p : ℕ}
    (Φ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin p) (Fin p) ℂ) :
    IsCompletelyPositive Φ ↔
      (refMap (Fin d) Φ
        (pureState (fun x : Fin d × Fin d => if x.1 = x.2 then (1 : ℂ) else 0))).PosSemidef := by
  sorry

/-- `Φ : M_d → M_p` is a PPT map iff its Choi matrix is positive and has positive partial
transpose. -/
theorem choi_isPPTMap_iff {d p : ℕ}
    (Φ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin p) (Fin p) ℂ) :
    IsPPTMap Φ ↔
      (refMap (Fin d) Φ
          (pureState (fun x : Fin d × Fin d => if x.1 = x.2 then (1 : ℂ) else 0))).PosSemidef ∧
        (partialTransposeRef (refMap (Fin d) Φ
          (pureState (fun x : Fin d × Fin d => if x.1 = x.2 then (1 : ℂ) else 0)))).PosSemidef := by
  sorry

/-- Horodecki–Shor–Ruskai for this definition: `Φ : M_d → M_p` is entanglement breaking iff its
Choi matrix is separable. -/
theorem choi_isEntanglementBreaking_iff {d p : ℕ}
    (Φ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin p) (Fin p) ℂ) :
    IsEntanglementBreaking Φ ↔
      PPTCompositionBound.IsSeparable (refMap (Fin d) Φ
        (pureState (fun x : Fin d × Fin d => if x.1 = x.2 then (1 : ℂ) else 0))) := by
  sorry

/-- Complete copositivity alone does not give complete positivity: transposition on `M_2` is
completely copositive but not completely positive. (So `IsPPTMap` must require both.) -/
theorem transposeMap_isCompletelyCopositive_not_isCompletelyPositive :
    IsCompletelyCopositive (transposeMap (Fin 2)) ∧
      ¬ IsCompletelyPositive (transposeMap (Fin 2)) := by
  sorry

/-- Order convention: `compList [Φ₁, Φ₂] = Φ₂ ∘ Φ₁`, so the head of the list acts first. -/
theorem compList_pair {d : ℕ} (Φ₁ Φ₂ : Module.End ℂ (Matrix (Fin d) (Fin d) ℂ)) :
    compList [Φ₁, Φ₂] = Φ₂ ∘ₗ Φ₁ := by
  sorry

/-- Index convention, smallest value: the zero map on `M_d` is PPT and its entanglement-breaking
index is `1` (powers start at `m = 1`). In particular a PPT map can have index below `2`. -/
theorem zero_map_isPPTMap_and_ebIndex_eq_one (d : ℕ) :
    IsPPTMap (0 : Module.End ℂ (Matrix (Fin d) (Fin d) ℂ)) ∧
      ebIndex (0 : Module.End ℂ (Matrix (Fin d) (Fin d) ℂ)) = 1 := by
  sorry

/-- Index convention, no such power: for `d ≥ 2` no power of the identity map on `M_d` is
entanglement breaking, and its entanglement-breaking index is `⊤`. -/
theorem ebIndex_id_eq_top (d : ℕ) (hd : 2 ≤ d) :
    ebIndex (LinearMap.id : Module.End ℂ (Matrix (Fin d) (Fin d) ℂ)) = ⊤ := by
  sorry

end PPTCompositionBound
