module

public import ThreeCopyQutritWerner.CertificateDescendantFrames2
public import ThreeCopyQutritWerner.CertificateDescendantSector0

@[expose] public section


/-!
# Complete sector-0 frames by the exact endpoint-register swap

The source matrices below are the original sector-0 archive matrices. Their
153 complete descendant frames have the same type and word labels as sector 2.
Both the signed lowering action and every source column are transported through
the already checked physical register swap. No new inverse data is introduced.
-/

noncomputable section

open scoped BigOperators Matrix

set_option maxRecDepth 100000

namespace ThreeCopyQutritWerner

def certificateDescendantFrames0Source : (t : Fin 7) →
    Matrix CertificateLocalWord (Fin (certificateDescendantFrames2SourceSize t)) ℤ := by
  exact
    Fin.cases (certificateLocalFrame0_0) <|
    Fin.cases (certificateLocalFrame0_1) <|
    Fin.cases (certificateLocalFrame0_2) <|
    Fin.cases (certificateLocalFrame0_3) <|
    Fin.cases (certificateLocalFrame0_4) <|
    Fin.cases (certificateLocalFrame0_5) <|
    Fin.cases (certificateLocalFrame0_6) <|
    Fin.rec0

theorem certificateDescendantFrames0Source_bound (t : Fin 7)
    (j : Fin (certificateDescendantFrames2SourceSize t)) :
    certificateSparseVector (certificateDescendantSeeds0
      (certificateDescendantFrames2SourceSeed t j)) =
        fun w => certificateDescendantFrames0Source t w j := by
  fin_cases t <;> fin_cases j <;>
    exact funext fun w => (certificateMatrixFromSparseEntries_eq_column _ w _).symm

theorem certificateDescendantFrames0Source_flip (t : Fin 7)
    (j : Fin (certificateDescendantFrames2SourceSize t)) :
    (fun w => certificateDescendantFrames0Source t w j) =
      fun w => certificateDescendantFrames2Source t (certificateFlipEnds w) j := by
  have h := certificateDescendantSeeds_flip (certificateDescendantFrames2SourceSeed t j)
  rw [certificateDescendantFrames0Source_bound, certificateDescendantFrames2Source_bound] at h
  exact h

def certificateDescendantFrames0Frame (f : Fin 153) :
    Matrix CertificateLocalWord
      (Fin (certificateDescendantFrames2SourceSize (certificateDescendantFrames2Type f))) ℤ :=
  certificateDescendantFrame (certificateLocalLowering {5})
    (certificateDescendantFrames0Source (certificateDescendantFrames2Type f))
    (certificateDescendantFrames2Lowering f)

/-- This is equality of the actual lowered frames, with no change of source columns. -/
theorem certificateDescendantFrames0Frame_flip (f : Fin 153)
    (w : CertificateLocalWord)
    (j : Fin (certificateDescendantFrames2SourceSize (certificateDescendantFrames2Type f))) :
    certificateDescendantFrames0Frame f w j =
      certificateDescendantFrames2Frame f (certificateFlipEnds w) j := by
  have h := certificateLoweringWord_flip_apply (certificateDescendantFrames2Lowering f)
    (fun w => certificateDescendantFrames2Source (certificateDescendantFrames2Type f) w j)
  rw [← certificateDescendantFrames0Source_flip] at h
  rw [← certificateDescendantFrame_column, ← certificateDescendantFrame_column] at h
  exact (congrFun h w).symm

def certificateDescendantFrames0Matrix :
    Matrix CertificateLocalWord CertificateDescendantFramesIndex2 ℤ :=
  certificateAssembleFrames _ certificateDescendantFrames0Frame

/-- The complete sector-0 frames span all physical words over the complex numbers. -/
theorem certificateDescendantFrames0Matrix_complex_surjective :
    Function.Surjective (certificateDescendantFrames0Matrix.map (Int.cast : ℤ → ℂ)).mulVec := by
  intro y
  obtain ⟨x, hx⟩ := certificateDescendantFrames2Matrix_complex_surjective
    (fun w => y (certificateFlipEnds w))
  refine ⟨x, ?_⟩
  ext w
  have h := congrFun hx (certificateFlipEnds w)
  change (∑ j, (certificateDescendantFrames0Frame j.1 w j.2 : ℂ) * x j) = y w
  simp only [certificateDescendantFrames0Frame_flip]
  simp only [certificateFlipEnds_involutive] at h
  exact h

/-- The sector-0 register swap preserves the full-frame bijection over the complex numbers. -/
theorem certificateDescendantFrames0Matrix_complex_bijective :
    Function.Bijective (certificateDescendantFrames0Matrix.map (Int.cast : ℤ → ℂ)).mulVec :=
  certificateMatrix_bijective_of_surjective_of_card_eq _ certificateDescendantFrames2index_card
    certificateDescendantFrames0Matrix_complex_surjective

/-- The sector-0 action keeps each original highest-frame multiplicity matrix intact. -/
theorem certificateDescendantFrames0Matrix_intertwines
    (M : Matrix CertificateLocalWord CertificateLocalWord ℂ)
    (A : (t : Fin 7) → Matrix (Fin (certificateDescendantFrames2SourceSize t))
      (Fin (certificateDescendantFrames2SourceSize t)) ℂ)
    (hcomm : ∀ g, M * (certificateLocalLowering {5} g).map (Int.cast : ℤ → ℂ) =
      (certificateLocalLowering {5} g).map (Int.cast : ℤ → ℂ) * M)
    (hsource : ∀ t, M * (certificateDescendantFrames0Source t).map (Int.cast : ℤ → ℂ) =
      (certificateDescendantFrames0Source t).map (Int.cast : ℤ → ℂ) * A t) :
    M * certificateDescendantFrames0Matrix.map (Int.cast : ℤ → ℂ) =
      certificateDescendantFrames0Matrix.map (Int.cast : ℤ → ℂ) *
        Matrix.blockDiagonal' (fun f => A (certificateDescendantFrames2Type f)) := by
  change M * certificateAssembleFrames _
      (fun f => (certificateDescendantFrames0Frame f).map (Int.cast : ℤ → ℂ)) =
    certificateAssembleFrames _
      (fun f => (certificateDescendantFrames0Frame f).map (Int.cast : ℤ → ℂ)) * _
  apply certificateAssembleFrames_intertwines
  intro f
  have hcast : (certificateDescendantFrames0Frame f).map (Int.cast : ℤ → ℂ) =
      certificateDescendantFrame (fun g => (certificateLocalLowering {5} g).map
        (Int.cast : ℤ → ℂ)) ((certificateDescendantFrames0Source
          (certificateDescendantFrames2Type f)).map (Int.cast : ℤ → ℂ))
        (certificateDescendantFrames2Lowering f) :=
    certificateDescendantFrame_map (Int.castRingHom ℂ) _ _ _
  rw [hcast]
  exact certificateDescendantFrame_intertwines _ M (A (certificateDescendantFrames2Type f))
    hcomm _ _ (hsource (certificateDescendantFrames2Type f))

end ThreeCopyQutritWerner
