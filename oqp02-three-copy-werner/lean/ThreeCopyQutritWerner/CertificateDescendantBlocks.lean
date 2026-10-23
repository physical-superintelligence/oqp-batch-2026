module

public import ThreeCopyQutritWerner.CertificateDescendants
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.NormNum

@[expose] public section


/-!
# Finite block inverses and explicit descendant programs

The checker lemmas keep every physical word and every generated column. The
only hypotheses are literal finite support equalities, a well-founded lowering
program, an exhaustive word reindexing, and exact block matrix inverses.
-/

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

private theorem sparseVector_zero_outside {n : Type*} [DecidableEq n]
    (L : List (n × ℤ)) (w : n) (h : ∀ a ∈ L, a.1 ≠ w) :
    certificateSparseVector L w = 0 := by
  apply List.sum_eq_zero
  intro z hz
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hz
  simp [h a ha]

/-- Equality on the union of the two finite supports is equality on all physical words. -/
theorem certificateSparseVector_eq_of_support {n : Type*} [DecidableEq n]
    (L M : List (n × ℤ))
    (h : List.Forall (fun a => certificateSparseVector L a.1 =
      certificateSparseVector M a.1) (L ++ M)) :
    certificateSparseVector L = certificateSparseVector M := by
  have hh := List.forall_iff_forall_mem.mp h
  ext w
  by_cases hw : ∃ a ∈ L ++ M, a.1 = w
  · obtain ⟨a, ha, rfl⟩ := hw
    exact hh a ha
  · have hL : ∀ a ∈ L, a.1 ≠ w :=
      fun a ha he => hw ⟨a, List.mem_append_left _ ha, he⟩
    have hM : ∀ a ∈ M, a.1 ≠ w :=
      fun a ha he => hw ⟨a, List.mem_append_right _ ha, he⟩
    rw [sparseVector_zero_outside L w hL, sparseVector_zero_outside M w hM]

/-- A sparse weight vector vanishes outside its declared weight. -/
theorem certificateSparseVector_zero_of_weight {n w : Type*} [DecidableEq n]
    (weight : n → w) (lam : w) (L : List (n × ℤ))
    (h : List.Forall (fun a => weight a.1 = lam) L) (r : n) (hr : weight r ≠ lam) :
    certificateSparseVector L r = 0 := by
  apply sparseVector_zero_outside
  intro a ha he
  apply hr
  rw [← he]
  exact List.forall_iff_forall_mem.mp h a ha

/-- Distinct declared weights and injective within-weight rows give globally
injective physical row coordinates. -/
theorem certificateWeightRows_injective {b n w : Type*} (size : b → ℕ)
    (rows : ∀ i, Fin (size i) → n) (weight : n → w) (lam : b → w)
    (hLam : Function.Injective lam) (hrows : ∀ i, Function.Injective (rows i))
    (hw : ∀ i j, weight (rows i j) = lam i) :
    Function.Injective (fun r : Σ i, Fin (size i) => rows r.1 r.2) := by
  rintro ⟨i, r⟩ ⟨j, s⟩ he
  change rows i r = rows j s at he
  have hweight := congrArg weight he
  rw [hw i r, hw j s] at hweight
  have hij : i = j := hLam hweight
  subst j
  have hrs : r = s := hrows i he
  subst s
  rfl

/-- The sparse physical matrix is block diagonal in its exhaustive weight rows. -/
theorem certificateSparseWeightBlocks_diagonal {b n w : Type*}
    [DecidableEq b] [DecidableEq n] (size : b → ℕ)
    (rows : ∀ i, Fin (size i) → n)
    (cols : ∀ i, Fin (size i) → List (n × ℤ))
    (weight : n → w) (lam : b → w) (hLam : Function.Injective lam)
    (A : ∀ i, Matrix (Fin (size i)) (Fin (size i)) ℤ)
    (hrow : ∀ i j, weight (rows i j) = lam i)
    (hcol : ∀ i j, List.Forall (fun a => weight a.1 = lam i) (cols i j))
    (hdiag : ∀ i r c, certificateSparseVector (cols i c) (rows i r) = A i r c) :
    (fun r c : (Σ i, Fin (size i)) =>
      certificateSparseVector (cols c.1 c.2) (rows r.1 r.2)) =
        Matrix.blockDiagonal' A := by
  funext r c
  rcases r with ⟨i, r⟩
  rcases c with ⟨j, c⟩
  by_cases hij : i = j
  · subst j
    rw [Matrix.blockDiagonal'_apply_eq]
    exact hdiag i r c
  · rw [Matrix.blockDiagonal'_apply_ne A (k := i) (k' := j) r c hij]
    apply certificateSparseVector_zero_of_weight weight (lam j) _ (hcol j c)
    rw [hrow]
    exact fun h => hij (hLam h)

/-- Decidability of a proposition defined by cases on a sum (`Sum.elim`). Program steps and
labels are stated with `Sum.elim` rather than an inline `match`, so that generated modules and
the generic lemmas share one term (inline matches elaborate to distinct auxiliary matchers). -/
instance certificateSumElimDecidable {α β : Type*} (P : α → Prop) (Q : β → Prop)
    [∀ a, Decidable (P a)] [∀ b, Decidable (Q b)] (x : α ⊕ β) : Decidable (Sum.elim P Q x) :=
  match x with
  | .inl a => (inferInstance : Decidable (P a))
  | .inr b => (inferInstance : Decidable (Q b))

/-- Every column in a finite acyclic lowering program is an actual descendant
of one of its specified source columns. -/
theorem certificateDescendantProgram_sound {n : Type*} [Fintype n]
    {count seeds : ℕ} (E : Fin 2 → Matrix n n ℤ)
    (V : Fin count → n → ℤ) (S : Fin seeds → n → ℤ)
    (step : Fin count → (Fin seeds ⊕ (Fin count × Fin 2)))
    (hstep : ∀ i, Sum.elim (fun s => V i = S s) (fun pg => V i = E pg.2 *ᵥ V pg.1) (step i))
    (hlt : ∀ i p g, step i = .inr (p, g) → p < i) :
    ∀ i, ∃ (s : Fin seeds) (word : List (Fin 2)),
      V i = word.foldl (fun x g => E g *ᵥ x) (S s) := by
  intro i
  induction i using Fin.strong_induction_on with
  | h i ih =>
      cases hs : step i with
      | inl s =>
          refine ⟨s, [], ?_⟩
          have h := hstep i
          rw [hs] at h
          simpa only [Sum.elim_inl, List.foldl_nil] using h
      | inr pg =>
          obtain ⟨s, word, hp⟩ := ih pg.1 (hlt i pg.1 pg.2 hs)
          refine ⟨s, word ++ [pg.2], ?_⟩
          simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
          rw [← hp]
          have h := hstep i
          rw [hs] at h
          simpa only [Sum.elim_inr] using h

/-- A matrix described in exhaustive physical row coordinates by square blocks
is surjective once every block has an exact right inverse. -/
theorem certificatePhysicalBlocks_surjective {b n R : Type*} [Fintype b]
    [DecidableEq b] [Fintype n] [Semiring R]
    (size : b → ℕ) (rows : (Σ i, Fin (size i)) → n)
    (hrows : Function.Surjective rows)
    (M : Matrix n (Σ i, Fin (size i)) R)
    (A B : ∀ i, Matrix (Fin (size i)) (Fin (size i)) R)
    (hM : M.submatrix rows id = Matrix.blockDiagonal' A)
    (hinv : ∀ i, A i * B i = 1) : Function.Surjective M.mulVec := by
  have hAB : M.submatrix rows id * Matrix.blockDiagonal' B = 1 := by
    rw [hM, ← Matrix.blockDiagonal'_mul]
    have h : (fun i => A i * B i) =
        (1 : ∀ i, Matrix (Fin (size i)) (Fin (size i)) R) := by
      funext i
      exact hinv i
    rw [h]
    exact Matrix.blockDiagonal'_one (m' := fun i => Fin (size i)) (α := R)
  intro y
  refine ⟨Matrix.blockDiagonal' B *ᵥ (y ∘ rows), ?_⟩
  ext w
  obtain ⟨r, rfl⟩ := hrows w
  have h := congrFun (congrArg (fun N => N *ᵥ (y ∘ rows)) hAB) r
  simp only [← Matrix.mulVec_mulVec, Matrix.one_mulVec] at h
  change (M *ᵥ (Matrix.blockDiagonal' B *ᵥ (y ∘ rows))) (rows r) = y (rows r) at h
  exact h

/-- An integer scaled right inverse becomes an exact rational right inverse. -/
theorem certificateRationalBlock_inverse {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℤ) (d : ℤ) (hd : d ≠ 0) (h : A * B = d • (1 : Matrix n n ℤ)) :
    A.map (Int.cast : ℤ → ℚ) * ((d : ℚ)⁻¹ • B.map (Int.cast : ℤ → ℚ)) = 1 := by
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd
  have hcast : A.map (Int.cast : ℤ → ℚ) * B.map (Int.cast : ℤ → ℚ) =
      (d : ℚ) • (1 : Matrix n n ℚ) := by
    ext i j
    have he := congrArg (Int.cast : ℤ → ℚ) (congrFun (congrFun h i) j)
    simpa [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] using he
  rw [Matrix.mul_smul, hcast, smul_smul, inv_mul_cancel₀ hdq, one_smul]

end ThreeCopyQutritWerner
