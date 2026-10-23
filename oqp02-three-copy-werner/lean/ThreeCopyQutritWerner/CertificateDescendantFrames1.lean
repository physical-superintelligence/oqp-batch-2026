module

public import ThreeCopyQutritWerner.CertificateDescendantFramesData1
public import ThreeCopyQutritWerner.CertificateDescendantPhysical1

@[expose] public section


/-! Exact physical binding and completeness of entire descendant frames.
The final action theorem retains explicit commutation and source-action premises. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

noncomputable section

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

theorem certificateDescendantFrames1Source_bound (t : Fin 8)
    (j : Fin (certificateDescendantFrames1SourceSize t)) :
    certificateSparseVector (certificateDescendantSeeds1 (certificateDescendantFrames1SourceSeed t j)) =
      fun w => certificateDescendantFrames1Source t w j := by
  fin_cases t <;> fin_cases j <;>
    exact funext fun w => (certificateMatrixFromSparseEntries_eq_column _ w _).symm

theorem certificateDescendantFrames1labels : ∀ i : Fin 729,
    Sum.elim (fun a => certificateDescendantFrames1Seed i = a ∧ certificateDescendantFrames1Word i = [])
      (fun pg => certificateDescendantFrames1Seed i = certificateDescendantFrames1Seed pg.1 ∧
        certificateDescendantFrames1Word i = certificateDescendantFrames1Word pg.1 ++ [pg.2])
      (certificateDescendantSteps1 i) := by
  intro i
  fin_cases i <;> decide

theorem certificateDescendantFrames1metadata : ∀ (f : Fin 190)
    (j : Fin (certificateDescendantFrames1SourceSize (certificateDescendantFrames1Type f))),
    certificateDescendantFrames1Seed (certificateDescendantFrames1Columns f j) = certificateDescendantFrames1SourceSeed (certificateDescendantFrames1Type f) j ∧
      certificateDescendantFrames1Word (certificateDescendantFrames1Columns f j) = certificateDescendantFrames1Lowering f := by
  intro f j
  fin_cases f <;> fin_cases j <;> decide

theorem certificateDescendantFrames1left_inv (j : CertificateDescendantFramesIndex1) :
    certificateDescendantFrames1Position (certificateDescendantFrames1Columns j.1 j.2) = j := by
  rcases j with ⟨f, j⟩
  fin_cases f <;> fin_cases j <;> decide

theorem certificateDescendantFrames1right_inv (i : Fin 729) :
    certificateDescendantFrames1Columns (certificateDescendantFrames1Position i).1 (certificateDescendantFrames1Position i).2 = i := by
  fin_cases i <;> decide

/-- Every selected column occurs exactly once as a full-frame column. -/
def certificateDescendantFrames1Equiv : CertificateDescendantFramesIndex1 ≃ Fin 729 where
  toFun j := certificateDescendantFrames1Columns j.1 j.2
  invFun := certificateDescendantFrames1Position
  left_inv := certificateDescendantFrames1left_inv
  right_inv := certificateDescendantFrames1right_inv

/-- Exact repetition count of each original local source type. -/
theorem certificateDescendantFrames1type_count (t : Fin 8) :
    (Finset.univ.filter (fun f : Fin 190 => certificateDescendantFrames1Type f = t)).card =
      certificateDescendantFrames1TypeCount t := by
  fin_cases t <;> decide

theorem certificateDescendantFrames1index_card :
    Fintype.card CertificateDescendantFramesIndex1 = Fintype.card CertificateLocalWord := by
  calc
    _ = Fintype.card (Fin 729) := Fintype.card_congr certificateDescendantFrames1Equiv
    _ = _ := by norm_num [CertificateLocalWord, Fintype.card_fun]

theorem certificateDescendantFrames1column_generated (i : Fin 729) :
    certificateSparseVector (certificateDescendantColumns1 i) =
      (certificateDescendantFrames1Word i).foldl (fun x g => certificateLocalLowering {0, 1, 2} g *ᵥ x)
        (certificateSparseVector (certificateDescendantSeeds1 (certificateDescendantFrames1Seed i))) :=
  certificateDescendantProgram_labels_sound (certificateLocalLowering {0, 1, 2})
    (fun i => certificateSparseVector (certificateDescendantColumns1 i))
    (fun a => certificateSparseVector (certificateDescendantSeeds1 a))
    certificateDescendantSteps1 certificateDescendantFrames1Seed certificateDescendantFrames1Word
    certificateDescendantSteps1_sound certificateDescendantSteps1_decreasing
    certificateDescendantFrames1labels i

/-- A full frame uses the original source matrix and exact physical lowering word. -/
def certificateDescendantFrames1Frame (f : Fin 190) :
    Matrix CertificateLocalWord (Fin (certificateDescendantFrames1SourceSize (certificateDescendantFrames1Type f))) ℤ :=
  certificateDescendantFrame (certificateLocalLowering {0, 1, 2})
    (certificateDescendantFrames1Source (certificateDescendantFrames1Type f)) (certificateDescendantFrames1Lowering f)

theorem certificateDescendantFrames1Frame_bound (f : Fin 190)
    (j : Fin (certificateDescendantFrames1SourceSize (certificateDescendantFrames1Type f))) :
    certificateSparseVector (certificateDescendantColumns1 (certificateDescendantFrames1Columns f j)) =
      fun w => certificateDescendantFrames1Frame f w j := by
  rw [certificateDescendantFrames1column_generated]
  obtain ⟨hs, hw⟩ := certificateDescendantFrames1metadata f j
  rw [hs, hw, certificateDescendantFrames1Source_bound]
  exact (certificateDescendantFrame_column _ _ _ _).symm

def certificateDescendantFrames1Matrix : Matrix CertificateLocalWord CertificateDescendantFramesIndex1 ℤ :=
  certificateAssembleFrames _ certificateDescendantFrames1Frame

theorem certificateDescendantFrames1Matrix_bound (w : CertificateLocalWord)
    (i : CertificateDescendantIndex1) :
    certificateDescendantPhysical1 w i =
      certificateDescendantFrames1Matrix w (certificateDescendantFrames1Position (certificateDescendantBlockColumns1 i.1 i.2)) := by
  let k := certificateDescendantBlockColumns1 i.1 i.2
  have h := congrFun (certificateDescendantFrames1Frame_bound (certificateDescendantFrames1Position k).1
    (certificateDescendantFrames1Position k).2) w
  rw [certificateDescendantFrames1right_inv] at h
  exact h

/-- The assembled full frames span the literal 729-dimensional complex physical space. -/
theorem certificateDescendantFrames1Matrix_complex_surjective :
    Function.Surjective (certificateDescendantFrames1Matrix.map (Int.cast : ℤ → ℂ)).mulVec := by
  classical
  apply certificateMatrix_surjective_of_columns _
    (certificateDescendantPhysical1.map (Int.cast : ℤ → ℂ))
    (fun i => certificateDescendantFrames1Position (certificateDescendantBlockColumns1 i.1 i.2))
  · intro w i
    exact congrArg (Int.cast : ℤ → ℂ) (certificateDescendantFrames1Matrix_bound w i)
  · exact certificateDescendantPhysical1_complex_surjective

/-- The full frames form a genuine basis-sized bijective physical matrix. -/
theorem certificateDescendantFrames1Matrix_complex_bijective :
    Function.Bijective (certificateDescendantFrames1Matrix.map (Int.cast : ℤ → ℂ)).mulVec :=
  certificateMatrix_bijective_of_surjective_of_card_eq _ certificateDescendantFrames1index_card
    certificateDescendantFrames1Matrix_complex_surjective

/-- Exact whole-frame action, with the original local column type on each diagonal block. -/
theorem certificateDescendantFrames1Matrix_intertwines
    (M : Matrix CertificateLocalWord CertificateLocalWord ℂ)
    (A : (t : Fin 8) → Matrix (Fin (certificateDescendantFrames1SourceSize t))
      (Fin (certificateDescendantFrames1SourceSize t)) ℂ)
    (hcomm : ∀ g, M * (certificateLocalLowering {0, 1, 2} g).map (Int.cast : ℤ → ℂ) =
      (certificateLocalLowering {0, 1, 2} g).map (Int.cast : ℤ → ℂ) * M)
    (hsource : ∀ t, M * (certificateDescendantFrames1Source t).map (Int.cast : ℤ → ℂ) =
      (certificateDescendantFrames1Source t).map (Int.cast : ℤ → ℂ) * A t) :
    M * certificateDescendantFrames1Matrix.map (Int.cast : ℤ → ℂ) =
      certificateDescendantFrames1Matrix.map (Int.cast : ℤ → ℂ) *
        Matrix.blockDiagonal' (fun f => A (certificateDescendantFrames1Type f)) := by
  change M * certificateAssembleFrames _ (fun f => (certificateDescendantFrames1Frame f).map (Int.cast : ℤ → ℂ)) =
    certificateAssembleFrames _ (fun f => (certificateDescendantFrames1Frame f).map (Int.cast : ℤ → ℂ)) * _
  apply certificateAssembleFrames_intertwines
  intro f
  have hcast : (certificateDescendantFrames1Frame f).map (Int.cast : ℤ → ℂ) =
      certificateDescendantFrame (fun g => (certificateLocalLowering {0, 1, 2} g).map
        (Int.cast : ℤ → ℂ)) ((certificateDescendantFrames1Source (certificateDescendantFrames1Type f)).map
        (Int.cast : ℤ → ℂ)) (certificateDescendantFrames1Lowering f) :=
    certificateDescendantFrame_map (Int.castRingHom ℂ) _ _ _
  rw [hcast]
  exact certificateDescendantFrame_intertwines _ M (A (certificateDescendantFrames1Type f))
    hcomm _ _ (hsource (certificateDescendantFrames1Type f))

end ThreeCopyQutritWerner
