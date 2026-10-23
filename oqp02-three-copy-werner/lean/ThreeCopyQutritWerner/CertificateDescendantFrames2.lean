module

public import ThreeCopyQutritWerner.CertificateDescendantFramesData2
public import ThreeCopyQutritWerner.CertificateDescendantPhysical

@[expose] public section


/-! Exact physical binding and completeness of entire descendant frames.
The final action theorem retains explicit commutation and source-action premises. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

noncomputable section

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

theorem certificateDescendantFrames2Source_bound (t : Fin 7)
    (j : Fin (certificateDescendantFrames2SourceSize t)) :
    certificateSparseVector (certificateDescendantSeeds2 (certificateDescendantFrames2SourceSeed t j)) =
      fun w => certificateDescendantFrames2Source t w j := by
  fin_cases t <;> fin_cases j <;>
    exact funext fun w => (certificateMatrixFromSparseEntries_eq_column _ w _).symm

theorem certificateDescendantFrames2labels : ∀ i : Fin 729,
    Sum.elim (fun a => certificateDescendantFrames2Seed i = a ∧ certificateDescendantFrames2Word i = [])
      (fun pg => certificateDescendantFrames2Seed i = certificateDescendantFrames2Seed pg.1 ∧
        certificateDescendantFrames2Word i = certificateDescendantFrames2Word pg.1 ++ [pg.2])
      (certificateDescendantSteps2 i) := by
  intro i
  fin_cases i <;> decide

theorem certificateDescendantFrames2metadata : ∀ (f : Fin 153)
    (j : Fin (certificateDescendantFrames2SourceSize (certificateDescendantFrames2Type f))),
    certificateDescendantFrames2Seed (certificateDescendantFrames2Columns f j) = certificateDescendantFrames2SourceSeed (certificateDescendantFrames2Type f) j ∧
      certificateDescendantFrames2Word (certificateDescendantFrames2Columns f j) = certificateDescendantFrames2Lowering f := by
  intro f j
  fin_cases f <;> fin_cases j <;> decide

theorem certificateDescendantFrames2left_inv (j : CertificateDescendantFramesIndex2) :
    certificateDescendantFrames2Position (certificateDescendantFrames2Columns j.1 j.2) = j := by
  rcases j with ⟨f, j⟩
  fin_cases f <;> fin_cases j <;> decide

theorem certificateDescendantFrames2right_inv (i : Fin 729) :
    certificateDescendantFrames2Columns (certificateDescendantFrames2Position i).1 (certificateDescendantFrames2Position i).2 = i := by
  fin_cases i <;> decide

/-- Every selected column occurs exactly once as a full-frame column. -/
def certificateDescendantFrames2Equiv : CertificateDescendantFramesIndex2 ≃ Fin 729 where
  toFun j := certificateDescendantFrames2Columns j.1 j.2
  invFun := certificateDescendantFrames2Position
  left_inv := certificateDescendantFrames2left_inv
  right_inv := certificateDescendantFrames2right_inv

/-- Exact repetition count of each original local source type. -/
theorem certificateDescendantFrames2type_count (t : Fin 7) :
    (Finset.univ.filter (fun f : Fin 153 => certificateDescendantFrames2Type f = t)).card =
      certificateDescendantFrames2TypeCount t := by
  fin_cases t <;> decide

theorem certificateDescendantFrames2index_card :
    Fintype.card CertificateDescendantFramesIndex2 = Fintype.card CertificateLocalWord := by
  calc
    _ = Fintype.card (Fin 729) := Fintype.card_congr certificateDescendantFrames2Equiv
    _ = _ := by norm_num [CertificateLocalWord, Fintype.card_fun]

theorem certificateDescendantFrames2column_generated (i : Fin 729) :
    certificateSparseVector (certificateDescendantColumns2 i) =
      (certificateDescendantFrames2Word i).foldl (fun x g => certificateLocalLowering {0} g *ᵥ x)
        (certificateSparseVector (certificateDescendantSeeds2 (certificateDescendantFrames2Seed i))) :=
  certificateDescendantProgram_labels_sound (certificateLocalLowering {0})
    (fun i => certificateSparseVector (certificateDescendantColumns2 i))
    (fun a => certificateSparseVector (certificateDescendantSeeds2 a))
    certificateDescendantSteps2 certificateDescendantFrames2Seed certificateDescendantFrames2Word
    certificateDescendantSteps2_sound certificateDescendantSteps2_decreasing
    certificateDescendantFrames2labels i

/-- A full frame uses the original source matrix and exact physical lowering word. -/
def certificateDescendantFrames2Frame (f : Fin 153) :
    Matrix CertificateLocalWord (Fin (certificateDescendantFrames2SourceSize (certificateDescendantFrames2Type f))) ℤ :=
  certificateDescendantFrame (certificateLocalLowering {0})
    (certificateDescendantFrames2Source (certificateDescendantFrames2Type f)) (certificateDescendantFrames2Lowering f)

theorem certificateDescendantFrames2Frame_bound (f : Fin 153)
    (j : Fin (certificateDescendantFrames2SourceSize (certificateDescendantFrames2Type f))) :
    certificateSparseVector (certificateDescendantColumns2 (certificateDescendantFrames2Columns f j)) =
      fun w => certificateDescendantFrames2Frame f w j := by
  rw [certificateDescendantFrames2column_generated]
  obtain ⟨hs, hw⟩ := certificateDescendantFrames2metadata f j
  rw [hs, hw, certificateDescendantFrames2Source_bound]
  exact (certificateDescendantFrame_column _ _ _ _).symm

def certificateDescendantFrames2Matrix : Matrix CertificateLocalWord CertificateDescendantFramesIndex2 ℤ :=
  certificateAssembleFrames _ certificateDescendantFrames2Frame

theorem certificateDescendantFrames2Matrix_bound (w : CertificateLocalWord)
    (i : CertificateDescendantIndex2) :
    certificateDescendantPhysical2 w i =
      certificateDescendantFrames2Matrix w (certificateDescendantFrames2Position (certificateDescendantBlockColumns2 i.1 i.2)) := by
  let k := certificateDescendantBlockColumns2 i.1 i.2
  have h := congrFun (certificateDescendantFrames2Frame_bound (certificateDescendantFrames2Position k).1
    (certificateDescendantFrames2Position k).2) w
  rw [certificateDescendantFrames2right_inv] at h
  exact h

/-- The assembled full frames span the literal 729-dimensional complex physical space. -/
theorem certificateDescendantFrames2Matrix_complex_surjective :
    Function.Surjective (certificateDescendantFrames2Matrix.map (Int.cast : ℤ → ℂ)).mulVec := by
  classical
  apply certificateMatrix_surjective_of_columns _
    (certificateDescendantPhysical2.map (Int.cast : ℤ → ℂ))
    (fun i => certificateDescendantFrames2Position (certificateDescendantBlockColumns2 i.1 i.2))
  · intro w i
    exact congrArg (Int.cast : ℤ → ℂ) (certificateDescendantFrames2Matrix_bound w i)
  · exact certificateDescendantPhysical2_complex_surjective

/-- The full frames form a genuine basis-sized bijective physical matrix. -/
theorem certificateDescendantFrames2Matrix_complex_bijective :
    Function.Bijective (certificateDescendantFrames2Matrix.map (Int.cast : ℤ → ℂ)).mulVec :=
  certificateMatrix_bijective_of_surjective_of_card_eq _ certificateDescendantFrames2index_card
    certificateDescendantFrames2Matrix_complex_surjective

/-- Exact whole-frame action, with the original local column type on each diagonal block. -/
theorem certificateDescendantFrames2Matrix_intertwines
    (M : Matrix CertificateLocalWord CertificateLocalWord ℂ)
    (A : (t : Fin 7) → Matrix (Fin (certificateDescendantFrames2SourceSize t))
      (Fin (certificateDescendantFrames2SourceSize t)) ℂ)
    (hcomm : ∀ g, M * (certificateLocalLowering {0} g).map (Int.cast : ℤ → ℂ) =
      (certificateLocalLowering {0} g).map (Int.cast : ℤ → ℂ) * M)
    (hsource : ∀ t, M * (certificateDescendantFrames2Source t).map (Int.cast : ℤ → ℂ) =
      (certificateDescendantFrames2Source t).map (Int.cast : ℤ → ℂ) * A t) :
    M * certificateDescendantFrames2Matrix.map (Int.cast : ℤ → ℂ) =
      certificateDescendantFrames2Matrix.map (Int.cast : ℤ → ℂ) *
        Matrix.blockDiagonal' (fun f => A (certificateDescendantFrames2Type f)) := by
  change M * certificateAssembleFrames _ (fun f => (certificateDescendantFrames2Frame f).map (Int.cast : ℤ → ℂ)) =
    certificateAssembleFrames _ (fun f => (certificateDescendantFrames2Frame f).map (Int.cast : ℤ → ℂ)) * _
  apply certificateAssembleFrames_intertwines
  intro f
  have hcast : (certificateDescendantFrames2Frame f).map (Int.cast : ℤ → ℂ) =
      certificateDescendantFrame (fun g => (certificateLocalLowering {0} g).map
        (Int.cast : ℤ → ℂ)) ((certificateDescendantFrames2Source (certificateDescendantFrames2Type f)).map
        (Int.cast : ℤ → ℂ)) (certificateDescendantFrames2Lowering f) :=
    certificateDescendantFrame_map (Int.castRingHom ℂ) _ _ _
  rw [hcast]
  exact certificateDescendantFrame_intertwines _ M (A (certificateDescendantFrames2Type f))
    hcomm _ _ (hsource (certificateDescendantFrames2Type f))

end ThreeCopyQutritWerner
