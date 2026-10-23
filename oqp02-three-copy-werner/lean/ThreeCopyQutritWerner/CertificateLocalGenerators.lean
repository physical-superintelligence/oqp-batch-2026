module

public import ThreeCopyQutritWerner.CertificateSparseFrames
public import Mathlib.Data.List.FinRange

@[expose] public section


/-!
# Signed local raising and lowering operators on the physical six-register basis

For a chosen set of fundamental registers, Eᵢⱼ replaces j by i with sign +1.
On every remaining dual register it replaces i by j with sign −1. The matrix
acts on column vectors; row words are the resulting words. This is the exact
signed word action used in the archive's local frame construction. The reverse
choice of i and j defines the lowering action without an additional convention.

The sector-0 frames were made by swapping registers 0 and 5 in sector 2;
therefore their signed fundamental set is {5}. This statement does not identify
these choices with a separately chosen physical group representation.
-/

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

abbrev CertificateLocalWord := Fin 6 → Fin 3

/-- Signed outputs of one local matrix-unit generator on a physical basis word. -/
def certificateLocalGeneratorWord (ket : Finset (Fin 6)) (i j : Fin 3)
    (w : CertificateLocalWord) : List (CertificateLocalWord × ℤ) :=
  (List.finRange 6).filterMap fun s =>
    if s ∈ ket then
      if w s = j then some (Function.update w s i, 1) else none
    else
      if w s = i then some (Function.update w s j, -1) else none

/-- The literal 729 by 729 integer generator, with output rows and input columns. -/
def certificateLocalGenerator (ket : Finset (Fin 6)) (i j : Fin 3) :
    Matrix CertificateLocalWord CertificateLocalWord ℤ :=
  fun r c => certificateSparseVector (certificateLocalGeneratorWord ket i j c) r

/-- The signed diagonal weight of a word at a selected local coordinate. -/
def certificateLocalWeight (ket : Finset (Fin 6)) (w : CertificateLocalWord)
    (i : Fin 3) : ℤ :=
  ∑ s : Fin 6, if w s = i then (if s ∈ ket then 1 else -1) else 0

/-- Apply a sparse word action to a sparse vector, keeping all repeated outputs. -/
def certificateSparseAction {n : Type*} (F : n → List (n × ℤ))
    (L : List (n × ℤ)) : List (n × ℤ) :=
  L.flatMap fun a => (F a.1).map fun b => (b.1, b.2 * a.2)

private theorem sparseVector_append {n : Type*} [DecidableEq n]
    (L M : List (n × ℤ)) (w : n) :
    certificateSparseVector (L ++ M) w =
      certificateSparseVector L w + certificateSparseVector M w := by
  simp [certificateSparseVector]

private theorem sparseVector_scale {n : Type*} [DecidableEq n]
    (L : List (n × ℤ)) (z : ℤ) (w : n) :
    certificateSparseVector (L.map fun a => (a.1, a.2 * z)) w =
      certificateSparseVector L w * z := by
  induction L with
  | nil => simp [certificateSparseVector]
  | cons a L ih =>
      simp only [List.map_cons, certificateSparseVector, List.sum_cons] at ih ⊢
      rw [ih, add_mul]
      by_cases h : a.1 = w <;> simp [h]

/-- Sparse application is exactly multiplication by the physical generator matrix. -/
theorem certificateSparseAction_eq_mulVec {n : Type*} [Fintype n] [DecidableEq n]
    (F : n → List (n × ℤ)) (L : List (n × ℤ)) :
    (fun r c => certificateSparseVector (F c) r : Matrix n n ℤ) *ᵥ certificateSparseVector L =
      certificateSparseVector (certificateSparseAction F L) := by
  let M : Matrix n n ℤ := fun r c => certificateSparseVector (F c) r
  change M *ᵥ certificateSparseVector L = certificateSparseVector (certificateSparseAction F L)
  induction L with
  | nil => ext w; simp [certificateSparseAction, certificateSparseVector, Matrix.mulVec, dotProduct]
  | cons a L ih =>
      ext w
      have hcons : certificateSparseVector (a :: L) =
          (fun v => if a.1 = v then a.2 else 0) + certificateSparseVector L := rfl
      rw [hcons, Matrix.mulVec_add, Pi.add_apply, ih]
      simp only [certificateSparseAction, List.flatMap_cons, sparseVector_append,
        sparseVector_scale]
      congr 1
      simp [M, Matrix.mulVec, dotProduct, mul_ite]

/-- Checking zero at each listed support word checks the entire physical vector. -/
theorem certificateSparseVector_eq_zero_of_support {n : Type*} [DecidableEq n]
    (L : List (n × ℤ))
    (h : List.Forall (fun a => certificateSparseVector L a.1 = 0) L) :
    certificateSparseVector L = 0 := by
  have hh := List.forall_iff_forall_mem.mp h
  ext w
  by_cases hw : ∃ a ∈ L, a.1 = w
  · obtain ⟨a, ha, rfl⟩ := hw
    exact hh a ha
  · change (L.map (fun a => if a.1 = w then a.2 else 0)).sum = 0
    apply List.sum_eq_zero
    intro z hz
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hz
    have hne : a.1 ≠ w := fun he => hw ⟨a, ha, he⟩
    simp [hne]

/-- Sparse support checks prove an actual column is killed by a physical generator. -/
theorem certificateLocalGenerator_annihilates_of_check {m : ℕ}
    (ket : Finset (Fin 6)) (i j : Fin 3)
    (entries : List (CertificateLocalWord × Fin m × ℤ)) (c : Fin m)
    (h : List.Forall (fun a => certificateSparseVector
      (certificateSparseAction (certificateLocalGeneratorWord ket i j)
        (certificateSparseFrameColumn entries c)) a.1 = 0)
      (certificateSparseAction (certificateLocalGeneratorWord ket i j)
        (certificateSparseFrameColumn entries c))) :
    certificateLocalGenerator ket i j *ᵥ
      (fun w => certificateMatrixFromSparseEntries entries w c) = 0 := by
  have hcol : (fun w => certificateMatrixFromSparseEntries entries w c) =
      certificateSparseVector (certificateSparseFrameColumn entries c) := by
    funext w
    exact certificateMatrixFromSparseEntries_eq_column entries w c
  rw [hcol]
  change (fun r s => certificateSparseVector (certificateLocalGeneratorWord ket i j s) r :
    Matrix CertificateLocalWord CertificateLocalWord ℤ) *ᵥ
      certificateSparseVector (certificateSparseFrameColumn entries c) = 0
  exact (certificateSparseAction_eq_mulVec (certificateLocalGeneratorWord ket i j)
      (certificateSparseFrameColumn entries c)).trans
        (certificateSparseVector_eq_zero_of_support _ h)

/-- A diagonal function is constant on a sparse support, so its vector is an eigenvector. -/
theorem certificateSparseVector_weight {n : Type*} [DecidableEq n]
    (f : n → ℤ) (lam : ℤ) (L : List (n × ℤ))
    (h : List.Forall (fun a => f a.1 = lam) L) (w : n) :
    f w * certificateSparseVector L w = lam * certificateSparseVector L w := by
  induction L with
  | nil => simp [certificateSparseVector]
  | cons a L ih =>
      obtain ⟨ha, hL⟩ := (List.forall_cons _ _ _).mp h
      have hi := ih hL
      simp only [certificateSparseVector, List.map_cons, List.sum_cons, mul_add] at hi ⊢
      rw [hi]
      by_cases hw : a.1 = w
      · simp [← hw, ha]
      · simp [hw]

/-- Weight checks refer to the actual local frame column on every physical word. -/
theorem certificateLocalFrame_weight_of_check {m : ℕ}
    (ket : Finset (Fin 6)) (lam : Fin 3 → ℤ)
    (entries : List (CertificateLocalWord × Fin m × ℤ)) (c : Fin m)
    (h : List.Forall (fun a => ∀ i, certificateLocalWeight ket a.1 i = lam i)
      (certificateSparseFrameColumn entries c)) (i : Fin 3) (w : CertificateLocalWord) :
    certificateLocalWeight ket w i * certificateMatrixFromSparseEntries entries w c =
      lam i * certificateMatrixFromSparseEntries entries w c := by
  rw [certificateMatrixFromSparseEntries_eq_column]
  exact certificateSparseVector_weight (fun v => certificateLocalWeight ket v i) (lam i)
    (certificateSparseFrameColumn entries c) (List.Forall.imp (fun _ ha => ha i) h) w

end ThreeCopyQutritWerner
