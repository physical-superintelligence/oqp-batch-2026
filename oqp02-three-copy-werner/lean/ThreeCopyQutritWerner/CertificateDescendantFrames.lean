module

public import ThreeCopyQutritWerner.CertificateDescendantBlocks
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Data.Complex.Basic
public import Mathlib.Data.Fintype.Order
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence

@[expose] public section


/-!
# Exact labels and complete descendant frames

The labels checked here specify the original source column and the ordered
lowering word, rather than merely asserting that some such labels exist.
The matrix lemmas assemble complete source frames with their original column
order. No commutation, highest-frame action, or positivity is assumed implicitly.
-/

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

/-- A checked acyclic program realizes its declared seed and lowering word. -/
theorem certificateDescendantProgram_labels_sound {n R : Type*} [Fintype n] [Semiring R]
    {count seeds : ℕ} (E : Fin 2 → Matrix n n R)
    (V : Fin count → n → R) (S : Fin seeds → n → R)
    (step : Fin count → (Fin seeds ⊕ (Fin count × Fin 2)))
    (seed : Fin count → Fin seeds) (word : Fin count → List (Fin 2))
    (hstep : ∀ i, Sum.elim (fun s => V i = S s) (fun pg => V i = E pg.2 *ᵥ V pg.1) (step i))
    (hlt : ∀ i p g, step i = .inr (p, g) → p < i)
    (hlabels : ∀ i, Sum.elim (fun s => seed i = s ∧ word i = [])
      (fun pg => seed i = seed pg.1 ∧ word i = word pg.1 ++ [pg.2]) (step i)) :
    ∀ i, V i = (word i).foldl (fun x g => E g *ᵥ x) (S (seed i)) := by
  intro i
  induction i using Fin.strong_induction_on with
  | h i ih =>
      cases hs : step i with
      | inl s =>
          have hl := hlabels i
          rw [hs] at hl
          simp only [Sum.elim_inl] at hl
          rw [hl.1, hl.2, List.foldl_nil]
          have h := hstep i
          rw [hs] at h
          simpa only [Sum.elim_inl] using h
      | inr pg =>
          have hl := hlabels i
          rw [hs] at hl
          simp only [Sum.elim_inr] at hl
          rw [hl.1, hl.2, List.foldl_append, List.foldl_cons, List.foldl_nil]
          rw [← ih pg.1 (hlt i pg.1 pg.2 hs)]
          have h := hstep i
          rw [hs] at h
          simpa only [Sum.elim_inr] using h

/-- Each column of a descendant frame is the same word acting on its source column. -/
theorem certificateDescendantFrame_column {n m R : Type*} [Fintype n] [Semiring R]
    (E : Fin 2 → Matrix n n R) (U : Matrix n m R) (word : List (Fin 2)) (j : m) :
    (fun w => certificateDescendantFrame E U word w j) =
      word.foldl (fun x g => E g *ᵥ x) (fun w => U w j) := by
  induction word generalizing U with
  | nil => rfl
  | cons g word ih =>
      change (fun w => certificateDescendantFrame E (E g * U) word w j) = _
      rw [ih]
      rfl

/-- Exact scalar change preserves the physical generator product and source frame. -/
theorem certificateDescendantFrame_map {n m R S : Type*} [Fintype n]
    [Semiring R] [Semiring S] (f : R →+* S)
    (E : Fin 2 → Matrix n n R) (U : Matrix n m R) (word : List (Fin 2)) :
    (certificateDescendantFrame E U word).map f =
      certificateDescendantFrame (fun g => (E g).map f) (U.map f) word := by
  induction word generalizing U with
  | nil => rfl
  | cons g word ih =>
      change (certificateDescendantFrame E (E g * U) word).map f = _
      rw [ih, Matrix.map_mul]
      rfl

/-- Assemble complete frames without identifying columns belonging to different frames. -/
def certificateAssembleFrames {b n R : Type*} (m : b → Type*)
    (V : ∀ i, Matrix n (m i) R) : Matrix n (Σ i, m i) R :=
  fun r c => V c.1 r c.2

/-- The block action has exactly the source-column convention used in each frame. -/
theorem certificateAssembleFrames_intertwines {b n R : Type*} {m : b → Type*}
    [Fintype b] [DecidableEq b] [Fintype n] [∀ i, Fintype (m i)] [Semiring R]
    (M : Matrix n n R) (V : ∀ i, Matrix n (m i) R)
    (A : ∀ i, Matrix (m i) (m i) R) (hV : ∀ i, M * V i = V i * A i) :
    M * certificateAssembleFrames m V =
      certificateAssembleFrames m V * Matrix.blockDiagonal' A := by
  ext r ⟨i, c⟩
  change (M * V i) r c = _
  rw [hV i]
  simp [Matrix.mul_apply, certificateAssembleFrames, Fintype.sum_sigma,
    Matrix.blockDiagonal'_apply', mul_dite]

/-- Repeated or reordered columns of a surjective matrix remain spanned by a larger
matrix containing those exact columns. This does not require a dimension assertion. -/
theorem certificateMatrix_surjective_of_columns {n m k R : Type*}
    [Fintype n] [Fintype m] [Fintype k] [DecidableEq k] [Semiring R]
    (V : Matrix n k R) (W : Matrix n m R) (col : m → k)
    (hcol : ∀ r j, W r j = V r (col j)) (hW : Function.Surjective W.mulVec) :
    Function.Surjective V.mulVec := by
  let T : Matrix k m R := fun i j => if i = col j then 1 else 0
  have hVT : V * T = W := by
    ext r j
    change (∑ i : k, V r i * (if i = col j then 1 else 0)) = W r j
    rw [hcol]
    simp [mul_ite]
  intro y
  obtain ⟨x, hx⟩ := hW y
  refine ⟨T *ᵥ x, ?_⟩
  rw [Matrix.mulVec_mulVec, hVT, hx]

/-- A physical full-frame spanning matrix of equal row and column dimensions is bijective. -/
theorem certificateMatrix_bijective_of_surjective_of_card_eq {n m : Type*}
    [Fintype n] [Fintype m] (M : Matrix n m ℂ)
    (hc : Fintype.card m = Fintype.card n) (hM : Function.Surjective M.mulVec) :
    Function.Bijective M.mulVec := by
  refine ⟨?_, hM⟩
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := M.mulVecLin) (by simpa only [Module.finrank_pi] using hc)).mpr
  exact hM

end ThreeCopyQutritWerner
