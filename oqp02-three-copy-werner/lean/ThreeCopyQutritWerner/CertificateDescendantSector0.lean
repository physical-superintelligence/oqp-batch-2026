module

public import ThreeCopyQutritWerner.CertificateDescendantPhysical

@[expose] public section


/-!
# Sector-0 completeness by exact register relabeling

The source sector-0 frames are obtained from sector 2 by swapping registers
0 and 5. This file reuses the entire sector-2 physical inverse and verifies the
signed-generator covariance and original-frame binding. No new block inverse,
representation dimension, or endpoint certificate is assumed.
-/

noncomputable section

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

/-- Swap the two endpoint registers, retaining the archive's six-word convention. -/
def certificateFlipEnds : Equiv.Perm CertificateLocalWord where
  toFun w := ![w 5, w 1, w 2, w 3, w 4, w 0]
  invFun w := ![w 5, w 1, w 2, w 3, w 4, w 0]
  left_inv w := by funext i; fin_cases i <;> rfl
  right_inv w := by funext i; fin_cases i <;> rfl

@[simp]
theorem certificateFlipEnds_involutive (w : CertificateLocalWord) :
    certificateFlipEnds (certificateFlipEnds w) = w :=
  certificateFlipEnds.left_inv w

/-- Relabeling a finite sparse support relabels the literal physical vector. -/
theorem certificateSparseVector_relabel {n : Type*} [DecidableEq n]
    (e : Equiv.Perm n) (L : List (n × ℤ)) (w : n) :
    certificateSparseVector (L.map fun a => (e a.1, a.2)) w =
      certificateSparseVector L (e.symm w) := by
  induction L with
  | nil => simp [certificateSparseVector]
  | cons a L ih =>
      simp only [List.map_cons, certificateSparseVector, List.sum_cons] at ih ⊢
      rw [ih]
      have he : (e a.1 = w) ↔ (a.1 = e.symm w) := by
        constructor
        · intro h
          simpa only [e.symm_apply_apply] using congrArg e.symm h
        · intro h
          rw [h, e.apply_symm_apply]
      by_cases h : a.1 = e.symm w
      · rw [if_pos (he.mpr h), if_pos h]
      · rw [if_neg (fun h' => h (he.mp h')), if_neg h]

/-- The sparse list for the simple lowering operator selected by `g`. -/
def certificateSimpleLoweringWord (ket : Finset (Fin 6)) (g : Fin 2)
    (w : CertificateLocalWord) : List (CertificateLocalWord × ℤ) :=
  if g = 0 then certificateLocalGeneratorWord ket 1 0 w
  else certificateLocalGeneratorWord ket 2 1 w

theorem certificateLocalLowering_entry (ket : Finset (Fin 6)) (g : Fin 2)
    (r c : CertificateLocalWord) :
    certificateLocalLowering ket g r c =
      certificateSparseVector (certificateSimpleLoweringWord ket g c) r := by
  by_cases hg : g = 0 <;>
    simp only [certificateLocalLowering, certificateSimpleLoweringWord, hg, if_true,
      if_false, certificateLocalGenerator]

/-- Check covariance on every one of the 729 input basis words, with at most
six sparse output terms per generator. The output support is checked exhaustively. -/
theorem certificateLoweringWord_flip (g : Fin 2) (c : CertificateLocalWord) :
    certificateSparseVector (certificateSimpleLoweringWord {5} g (certificateFlipEnds c)) =
      certificateSparseVector ((certificateSimpleLoweringWord {0} g c).map
        fun a => (certificateFlipEnds a.1, a.2)) := by
  apply certificateSparseVector_eq_of_support
  have hcheck : ∀ g : Fin 2, ∀ c : CertificateLocalWord,
      List.Forall (fun a =>
        certificateSparseVector (certificateSimpleLoweringWord {5} g (certificateFlipEnds c)) a.1 =
        certificateSparseVector ((certificateSimpleLoweringWord {0} g c).map
          fun z => (certificateFlipEnds z.1, z.2)) a.1)
        (certificateSimpleLoweringWord {5} g (certificateFlipEnds c) ++
          (certificateSimpleLoweringWord {0} g c).map fun z => (certificateFlipEnds z.1, z.2)) := by
    intro g
    fin_cases g <;> decide
  exact hcheck g c

/-- The actual physical matrices transform by the same endpoint-register swap. -/
theorem certificateLowering_flip_entries (g : Fin 2) (r c : CertificateLocalWord) :
    certificateLocalLowering {5} g (certificateFlipEnds r) (certificateFlipEnds c) =
      certificateLocalLowering {0} g r c := by
  rw [certificateLocalLowering_entry, certificateLocalLowering_entry]
  rw [certificateLoweringWord_flip, certificateSparseVector_relabel]
  exact congrArg (certificateSparseVector (certificateSimpleLoweringWord {0} g c))
    (certificateFlipEnds.symm_apply_apply r)

/-- Lowering commutes with the physical row relabeling, for arbitrary vectors. -/
theorem certificateLowering_flip_mulVec (g : Fin 2) (v : CertificateLocalWord → ℤ) :
    (fun w => (certificateLocalLowering {0} g *ᵥ v) (certificateFlipEnds w)) =
      certificateLocalLowering {5} g *ᵥ (fun w => v (certificateFlipEnds w)) := by
  ext w
  symm
  simp only [Matrix.mulVec, dotProduct]
  refine Fintype.sum_equiv certificateFlipEnds _ _ ?_
  intro c
  have he := certificateLowering_flip_entries g (certificateFlipEnds w) (certificateFlipEnds c)
  simp only [certificateFlipEnds_involutive] at he
  rw [he]

/-- Transport an ordered lowering word through the exact signed relabeling. -/
theorem certificateLoweringWord_flip_apply (word : List (Fin 2)) (v : CertificateLocalWord → ℤ) :
    (fun w => (word.foldl (fun x g => certificateLocalLowering {0} g *ᵥ x) v)
      (certificateFlipEnds w)) =
      word.foldl (fun x g => certificateLocalLowering {5} g *ᵥ x)
        (fun w => v (certificateFlipEnds w)) := by
  induction word generalizing v with
  | nil => rfl
  | cons g word ih =>
      simp only [List.foldl_cons]
      rw [ih, certificateLowering_flip_mulVec]

/-- The original source-bound highest columns in sector 0. -/
def certificateDescendantSeeds0 : Fin 51 → List (CertificateLocalWord × ℤ) :=
  ![certificateSparseFrameColumn certificateLocalFrameEntries0_0 0,
    certificateSparseFrameColumn certificateLocalFrameEntries0_1 0,
    certificateSparseFrameColumn certificateLocalFrameEntries0_1 1,
    certificateSparseFrameColumn certificateLocalFrameEntries0_1 2,
    certificateSparseFrameColumn certificateLocalFrameEntries0_1 3,
    certificateSparseFrameColumn certificateLocalFrameEntries0_2 0,
    certificateSparseFrameColumn certificateLocalFrameEntries0_2 1,
    certificateSparseFrameColumn certificateLocalFrameEntries0_2 2,
    certificateSparseFrameColumn certificateLocalFrameEntries0_2 3,
    certificateSparseFrameColumn certificateLocalFrameEntries0_2 4,
    certificateSparseFrameColumn certificateLocalFrameEntries0_3 0,
    certificateSparseFrameColumn certificateLocalFrameEntries0_3 1,
    certificateSparseFrameColumn certificateLocalFrameEntries0_3 2,
    certificateSparseFrameColumn certificateLocalFrameEntries0_3 3,
    certificateSparseFrameColumn certificateLocalFrameEntries0_3 4,
    certificateSparseFrameColumn certificateLocalFrameEntries0_4 0,
    certificateSparseFrameColumn certificateLocalFrameEntries0_4 1,
    certificateSparseFrameColumn certificateLocalFrameEntries0_4 2,
    certificateSparseFrameColumn certificateLocalFrameEntries0_4 3,
    certificateSparseFrameColumn certificateLocalFrameEntries0_4 4,
    certificateSparseFrameColumn certificateLocalFrameEntries0_4 5,
    certificateSparseFrameColumn certificateLocalFrameEntries0_4 6,
    certificateSparseFrameColumn certificateLocalFrameEntries0_4 7,
    certificateSparseFrameColumn certificateLocalFrameEntries0_4 8,
    certificateSparseFrameColumn certificateLocalFrameEntries0_4 9,
    certificateSparseFrameColumn certificateLocalFrameEntries0_4 10,
    certificateSparseFrameColumn certificateLocalFrameEntries0_4 11,
    certificateSparseFrameColumn certificateLocalFrameEntries0_4 12,
    certificateSparseFrameColumn certificateLocalFrameEntries0_4 13,
    certificateSparseFrameColumn certificateLocalFrameEntries0_4 14,
    certificateSparseFrameColumn certificateLocalFrameEntries0_5 0,
    certificateSparseFrameColumn certificateLocalFrameEntries0_5 1,
    certificateSparseFrameColumn certificateLocalFrameEntries0_5 2,
    certificateSparseFrameColumn certificateLocalFrameEntries0_5 3,
    certificateSparseFrameColumn certificateLocalFrameEntries0_5 4,
    certificateSparseFrameColumn certificateLocalFrameEntries0_5 5,
    certificateSparseFrameColumn certificateLocalFrameEntries0_5 6,
    certificateSparseFrameColumn certificateLocalFrameEntries0_5 7,
    certificateSparseFrameColumn certificateLocalFrameEntries0_5 8,
    certificateSparseFrameColumn certificateLocalFrameEntries0_5 9,
    certificateSparseFrameColumn certificateLocalFrameEntries0_6 0,
    certificateSparseFrameColumn certificateLocalFrameEntries0_6 1,
    certificateSparseFrameColumn certificateLocalFrameEntries0_6 2,
    certificateSparseFrameColumn certificateLocalFrameEntries0_6 3,
    certificateSparseFrameColumn certificateLocalFrameEntries0_6 4,
    certificateSparseFrameColumn certificateLocalFrameEntries0_6 5,
    certificateSparseFrameColumn certificateLocalFrameEntries0_6 6,
    certificateSparseFrameColumn certificateLocalFrameEntries0_6 7,
    certificateSparseFrameColumn certificateLocalFrameEntries0_6 8,
    certificateSparseFrameColumn certificateLocalFrameEntries0_6 9,
    certificateSparseFrameColumn certificateLocalFrameEntries0_6 10]

/-- The relabeled sector-2 sources equal the actual archive's sector-0 sources. -/
theorem certificateDescendantSeeds_flip (s : Fin 51) :
    certificateSparseVector (certificateDescendantSeeds0 s) =
      fun w => certificateSparseVector (certificateDescendantSeeds2 s) (certificateFlipEnds w) := by
  have he : certificateSparseVector (certificateDescendantSeeds0 s) =
      certificateSparseVector ((certificateDescendantSeeds2 s).map
        fun a => (certificateFlipEnds a.1, a.2)) := by
    apply certificateSparseVector_eq_of_support
    fin_cases s <;> decide
  rw [he]
  funext w
  exact certificateSparseVector_relabel certificateFlipEnds (certificateDescendantSeeds2 s) w

/-- Reuse the entire sector-2 physical spanning matrix by swapping its endpoint rows. -/
def certificateDescendantPhysical0 : Matrix CertificateLocalWord CertificateDescendantIndex2 ℤ :=
  certificateDescendantPhysical2.submatrix certificateFlipEnds id

theorem certificateDescendantPhysical0_complex_surjective :
    Function.Surjective (certificateDescendantPhysical0.map (Int.cast : ℤ → ℂ)).mulVec := by
  intro y
  obtain ⟨x, hx⟩ := certificateDescendantPhysical2_complex_surjective
    (fun w => y (certificateFlipEnds w))
  refine ⟨x, ?_⟩
  ext w
  have h := congrFun hx (certificateFlipEnds w)
  simp only [certificateFlipEnds_involutive] at h
  show (certificateDescendantPhysical2.map (Int.cast : ℤ → ℂ) *ᵥ x) (certificateFlipEnds w) = y w
  exact h

theorem certificateDescendantPhysical0_generated (j : CertificateDescendantIndex2) :
    ∃ s : Fin 51, ∃ word : List (Fin 2),
      (fun w => certificateDescendantPhysical0 w j) =
        word.foldl (fun x g => certificateLocalLowering {5} g *ᵥ x)
          (certificateSparseVector (certificateDescendantSeeds0 s)) := by
  obtain ⟨s, word, h⟩ := certificateDescendantPhysical2_generated j
  refine ⟨s, word, ?_⟩
  have he := congrArg (fun v : CertificateLocalWord → ℤ => fun w => v (certificateFlipEnds w)) h
  rw [certificateLoweringWord_flip_apply, ← certificateDescendantSeeds_flip] at he
  exact he

/-- Full physical spanning and exact original-source generation in signed sector 0. -/
theorem certificateDescendantPhysical0_complete :
    Function.Surjective (certificateDescendantPhysical0.map (Int.cast : ℤ → ℂ)).mulVec ∧
      ∀ j : CertificateDescendantIndex2, ∃ s : Fin 51, ∃ word : List (Fin 2),
        (fun w => certificateDescendantPhysical0 w j) =
          word.foldl (fun x g => certificateLocalLowering {5} g *ᵥ x)
            (certificateSparseVector (certificateDescendantSeeds0 s)) :=
  ⟨certificateDescendantPhysical0_complex_surjective, certificateDescendantPhysical0_generated⟩

end ThreeCopyQutritWerner
