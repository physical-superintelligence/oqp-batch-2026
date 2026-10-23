module

public import ThreeCopyQutritWerner.BinaryPartitionTensor

@[expose] public section


/-!
# Explicit placement of the singled-out binary site

The three choices use exactly the manuscript's identity, siteEquiv₂, and
siteEquiv₃ placements. Within the remaining pair, the original site order
is retained. These coordinate identities perform no physical operation.
-/

noncomputable section

open scoped Matrix Kronecker

namespace ThreeCopyQutritWerner

/-- Place the selected original site first, retaining the other sites' order. -/
def binaryPartitionSiteTuple (i : Fin 3) :
    (Fin 2 × Fin 2 × Fin 2) ≃ (Fin 2 × Fin 2 × Fin 2) :=
  ![Equiv.refl _, siteEquiv₂, siteEquiv₃] i

/-- The same placement in the faithful finite-word coordinates. -/
def binaryPartitionSiteWord (i : Fin 3) :
    (Fin 2 × Fin 2 × Fin 2) ≃ (Fin 3 → Fin 2) :=
  (binaryPartitionSiteTuple i).trans binaryThreeWordEquiv.symm

/-- First of the two sites remaining after selecting i. -/
def binaryPartitionOtherFirst (i : Fin 3) : Fin 3 := ![1, 0, 0] i

theorem binaryPartitionSiteWord_entry (i j : Fin 3) (a : Fin 2 × Fin 2 × Fin 2) :
    binaryPartitionSiteWord i a j =
      if j = i then a.1 else if j = binaryPartitionOtherFirst i then a.2.1 else a.2.2 := by
  fin_cases i <;> fin_cases j <;>
    simp [binaryPartitionSiteWord, binaryPartitionSiteTuple, binaryPartitionOtherFirst,
      binaryThreeWordEquiv, siteEquiv₂, siteEquiv₃] <;> rfl

theorem binaryPartitionSiteWord_singleton (i : Fin 3) (a : Fin 2 × Fin 2 × Fin 2) :
    (fun j : ({i} : Finset (Fin 3)) => binaryPartitionSiteWord i a j) =
      (fun _ => a.1) := by
  funext j
  have hj : (j : Fin 3) = i := Finset.mem_singleton.mp j.property
  simp [binaryPartitionSiteWord_entry, hj]

theorem binaryPartitionSiteWord_complement (i : Fin 3) (a : Fin 2 × Fin 2 × Fin 2) :
    (fun j : ↥(({i} : Finset (Fin 3))ᶜ) => binaryPartitionSiteWord i a j) =
      (fun j : ↥(({i} : Finset (Fin 3))ᶜ) =>
        if (j : Fin 3) = binaryPartitionOtherFirst i then a.2.1 else a.2.2) := by
  funext j
  have hj : (j : Fin 3) ≠ i := by
    intro h
    exact (Finset.mem_compl.mp j.property) (Finset.mem_singleton.mpr h)
  simp [binaryPartitionSiteWord_entry, hj]

/-- A singleton first partition is literally one rank-one matrix tensored
with a two-site skew two-ray matrix in the selected original placement. -/
theorem binaryPartition_singleton_kronecker (i : Fin 3)
    (p q : (({i} : Finset (Fin 3)) → Fin 2) → ℂ)
    (r s : (↥(({i} : Finset (Fin 3))ᶜ) → Fin 2) → ℂ) :
    ∃ p' q' : Fin 2 → ℂ, ∃ r' s' : (Fin 2 × Fin 2) → ℂ,
      (binaryPartitionMatrix {i} p q r s).submatrix
        (binaryPartitionSiteWord i) (binaryPartitionSiteWord i) =
          (fun a b => p' a * q' b) ⊗ₖ (fun a b => r' a * s' b - s' a * r' b) := by
  let p' : Fin 2 → ℂ := fun a => p (fun _ => a)
  let q' : Fin 2 → ℂ := fun a => q (fun _ => a)
  let r' : (Fin 2 × Fin 2) → ℂ := fun a =>
    r (fun j => if (j : Fin 3) = binaryPartitionOtherFirst i then a.1 else a.2)
  let s' : (Fin 2 × Fin 2) → ℂ := fun a =>
    s (fun j => if (j : Fin 3) = binaryPartitionOtherFirst i then a.1 else a.2)
  refine ⟨p', q', r', s', ?_⟩
  ext a b
  simp only [Matrix.submatrix_apply, binaryPartitionMatrix, Matrix.kronecker, Matrix.kroneckerMap,
    binaryPartitionSiteWord_singleton, binaryPartitionSiteWord_complement]
  rfl

/-- With a singleton complementary partition, the selected first site
carries the skew factor and the remaining two sites carry the rank-one factor. -/
theorem binaryPartition_complement_singleton_kronecker (i : Fin 3)
    (p q : (↥(({i} : Finset (Fin 3))ᶜ) → Fin 2) → ℂ)
    (r s : (↥((({i} : Finset (Fin 3))ᶜ)ᶜ) → Fin 2) → ℂ) :
    ∃ p' q' : (Fin 2 × Fin 2) → ℂ, ∃ r' s' : Fin 2 → ℂ,
      (binaryPartitionMatrix ({i}ᶜ) p q r s).submatrix
        (binaryPartitionSiteWord i) (binaryPartitionSiteWord i) =
          (fun a b => r' a * s' b - s' a * r' b) ⊗ₖ (fun a b => p' a * q' b) := by
  have hsingle (a : Fin 2 × Fin 2 × Fin 2) :
      (fun j : ↥((({i} : Finset (Fin 3))ᶜ)ᶜ) => binaryPartitionSiteWord i a j) =
        (fun _ => a.1) := by
    funext j
    have hj : (j : Fin 3) = i :=
      Finset.mem_singleton.mp (Finset.notMem_compl.mp (Finset.mem_compl.mp j.property))
    simp [binaryPartitionSiteWord_entry, hj]
  let p' : (Fin 2 × Fin 2) → ℂ := fun a =>
    p (fun j => if (j : Fin 3) = binaryPartitionOtherFirst i then a.1 else a.2)
  let q' : (Fin 2 × Fin 2) → ℂ := fun a =>
    q (fun j => if (j : Fin 3) = binaryPartitionOtherFirst i then a.1 else a.2)
  let r' : Fin 2 → ℂ := fun a => r (fun _ => a)
  let s' : Fin 2 → ℂ := fun a => s (fun _ => a)
  refine ⟨p', q', r', s', ?_⟩
  ext a b
  simp only [Matrix.submatrix_apply, binaryPartitionMatrix,
    Matrix.kronecker, Matrix.kroneckerMap, Matrix.of_apply, hsingle,
    binaryPartitionSiteWord_complement]
  dsimp only [p', q', r', s']
  ring

end ThreeCopyQutritWerner
