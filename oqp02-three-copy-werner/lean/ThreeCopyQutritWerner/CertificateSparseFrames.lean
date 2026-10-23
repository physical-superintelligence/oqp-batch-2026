module

public import ThreeCopyQutritWerner.CertificateLocalFramesData
public import Mathlib.Algebra.BigOperators.Ring.List
public import Mathlib.Tactic.FinCases

@[expose] public section


/-!
# Sparse finite checks of the archive's original local Gram metrics

The generic dot-product identity below evaluates only pairs of nonzero support
entries. The concrete checks use ordinary kernel `decide` on small integer sums.
They do not assert highest-weight completeness, invertibility or endpoint sign.
-/

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

/-- A finite supported vector, retaining multiplicities in its list of entries. -/
def certificateSparseVector {n R : Type*} [DecidableEq n] [AddCommMonoid R]
    (entries : List (n × R)) (w : n) : R :=
  (entries.map (fun e => if e.1 = w then e.2 else 0)).sum

/-- Sum over the support of the first vector rather than the entire physical basis. -/
theorem certificateSparseVector_dot {n R : Type*} [Fintype n] [DecidableEq n]
    [CommSemiring R] (L M : List (n × R)) :
    (∑ w : n, certificateSparseVector L w * certificateSparseVector M w) =
      (L.map (fun a => a.2 * certificateSparseVector M a.1)).sum := by
  induction L with
  | nil => simp [certificateSparseVector]
  | cons a L ih =>
      have hcons : ∀ w : n, certificateSparseVector (a :: L) w =
          (if a.1 = w then a.2 else 0) + certificateSparseVector L w := fun _ => rfl
      simp only [hcons, add_mul, Finset.sum_add_distrib, List.map_cons, List.sum_cons]
      rw [ih]
      congr 1
      simp [ite_mul]

/-- The exact dot product as support-pair arithmetic, without a basis-size factor. -/
theorem certificateSparseVector_dot_pairs {n R : Type*} [Fintype n] [DecidableEq n]
    [CommSemiring R] (L M : List (n × R)) :
    (∑ w : n, certificateSparseVector L w * certificateSparseVector M w) =
      (L.map (fun a => (M.map
        (fun b => if a.1 = b.1 then a.2 * b.2 else 0)).sum)).sum := by
  rw [certificateSparseVector_dot]
  apply congrArg List.sum
  apply List.map_congr_left
  intro a _
  rw [certificateSparseVector, ← List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro b _
  by_cases h : a.1 = b.1 <;> simp [h, eq_comm]

/-- Select one column of a finite supported matrix. -/
def certificateSparseFrameColumn {m : ℕ}
    (entries : List ((Fin 6 → Fin 3) × Fin m × ℤ)) (j : Fin m) :
    List ((Fin 6 → Fin 3) × ℤ) :=
  entries.filterMap (fun e => if e.2.1 = j then some (e.1, e.2.2) else none)

theorem certificateMatrixFromSparseEntries_eq_column {m : ℕ}
    (entries : List ((Fin 6 → Fin 3) × Fin m × ℤ)) (w : Fin 6 → Fin 3) (j : Fin m) :
    certificateMatrixFromSparseEntries entries w j =
      certificateSparseVector (certificateSparseFrameColumn entries j) w := by
  induction entries with
  | nil => simp [certificateMatrixFromSparseEntries, certificateSparseVector,
      certificateSparseFrameColumn]
  | cons a L ih =>
      by_cases h : a.2.1 = j
      · simpa [certificateMatrixFromSparseEntries, certificateSparseVector,
          certificateSparseFrameColumn, h] using
          congrArg (fun z => (if a.1 = w then a.2.2 else 0) + z) ih
      · simpa [certificateMatrixFromSparseEntries, certificateSparseVector,
          certificateSparseFrameColumn, h] using ih

/-- Integer check expression for one entry of the original Gram matrix. -/
def certificateSparseFrameGramEntry {m : ℕ}
    (entries : List ((Fin 6 → Fin 3) × Fin m × ℤ)) (i j : Fin m) : ℤ :=
  ((certificateSparseFrameColumn entries i).map (fun a =>
    ((certificateSparseFrameColumn entries j).map
      (fun b => if a.1 = b.1 then a.2 * b.2 else 0)).sum)).sum

/-- The support-pair expression is the literal physical Gram entry. -/
theorem certificateSparseFrame_gram {m : ℕ}
    (entries : List ((Fin 6 → Fin 3) × Fin m × ℤ)) (i j : Fin m) :
    ((certificateMatrixFromSparseEntries entries)ᵀ *
      certificateMatrixFromSparseEntries entries) i j =
        certificateSparseFrameGramEntry entries i j := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply,
    certificateMatrixFromSparseEntries_eq_column]
  exact certificateSparseVector_dot_pairs _ _

end ThreeCopyQutritWerner
