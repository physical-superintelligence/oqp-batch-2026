module

public import ThreeCopyQutritWerner.CertificateFrameRealization
public import ThreeCopyQutritWerner.CertificateDescendantGram0
public import ThreeCopyQutritWerner.CertificateDescendantGram1
public import ThreeCopyQutritWerner.CertificateLocalDecomposition0
public import ThreeCopyQutritWerner.CertificateLocalDecomposition1
public import ThreeCopyQutritWerner.CertificateLocalDecomposition2

@[expose] public section


/-!
# Unconditional local physical realization in all three archive sectors

The literal original metrics and exact complete descendant bases discharge every
basis and scalar-overlap premise. Only positivity of the proposed coefficient
blocks in the original metric remains as input.
-/

noncomputable section

open scoped Matrix ComplexOrder

namespace ThreeCopyQutritWerner

theorem certificateLocalRealization0Gram_map (t : Fin 7) :
    (certificateDescendantGram0G t).map (Int.cast : ℤ → ℂ) =
      certificateLocalDecomposition0Gram t := by
  fin_cases t <;> rfl

theorem certificateLocalRealization0size_pos (t : Fin 7) :
    0 < certificateDescendantFrames2SourceSize t := by
  fin_cases t <;> decide

/-- The checked integer Gram is exactly the full complex physical Gram. -/
theorem certificateLocalRealization0gram :
    (certificateDescendantFrames0Matrix.map (Int.cast : ℤ → ℂ))ᴴ *
        certificateDescendantFrames0Matrix.map (Int.cast : ℤ → ℂ) =
      certificateRepeatedFrameMetric certificateDescendantFrames2SourceSize
        certificateDescendantFrames2Type certificateLocalDecomposition0Gram
          (certificateDescendantGram2K.map (Int.cast : ℤ → ℂ)) := by
  have h := certificate_integer_gram_complex _ _ certificateDescendantGram0_physical
  change _ = (certificateRepeatedFrameMetric certificateDescendantFrames2SourceSize
    certificateDescendantFrames2Type certificateDescendantGram0G
      certificateDescendantGram2K).map (Int.castRingHom ℂ) at h
  rw [certificateRepeatedFrameMetric_map] at h
  simpa only [Int.coe_castRingHom, certificateLocalRealization0Gram_map] using h

/-- The scalar frame metric is positive because it comes from actual columns. -/
theorem certificateLocalRealization0scalar_posSemidef :
    (certificateDescendantGram2K.map (Int.cast : ℤ → ℂ)).PosSemidef := by
  apply certificate_scalar_metric_posSemidef_of_gram
    certificateDescendantFrames2SourceSize certificateDescendantFrames2Type
    (fun t => ⟨0, certificateLocalRealization0size_pos t⟩)
    (certificateDescendantFrames0Matrix.map (Int.cast : ℤ → ℂ))
    certificateLocalDecomposition0Gram _ certificateLocalDecomposition0Gram_posDef
    certificateLocalRealization0gram
  intro f g hfg
  change (certificateDescendantGram2K f g : ℂ) = 0
  rw [certificateDescendantGram2K_off_type f g hfg, Int.cast_zero]

/-- Any original-metric positive local block tuple constructs a positive physical operator. -/
theorem certificateLocalRealization0_exists
    (A : (t : Fin 7) → Matrix (Fin (certificateDescendantFrames2SourceSize t))
      (Fin (certificateDescendantFrames2SourceSize t)) ℂ)
    (hA : ∀ t, (certificateLocalDecomposition0Gram t * A t).PosSemidef) :
    ∃ M : Matrix CertificateLocalWord CertificateLocalWord ℂ, M.PosSemidef ∧
      M * certificateDescendantFrames0Matrix.map (Int.cast : ℤ → ℂ) =
        certificateDescendantFrames0Matrix.map (Int.cast : ℤ → ℂ) *
          Matrix.blockDiagonal' (fun f => A (certificateDescendantFrames2Type f)) := by
  apply certificate_exists_positive_frame_realization
    certificateDescendantFrames2SourceSize certificateDescendantFrames2Type
    (fun t => ⟨0, certificateLocalRealization0size_pos t⟩)
    (certificateDescendantFrames0Matrix.map (Int.cast : ℤ → ℂ))
    certificateLocalDecomposition0Gram A
    (certificateDescendantGram2K.map (Int.cast : ℤ → ℂ))
    certificateDescendantFrames0Matrix_complex_bijective
    certificateLocalDecomposition0Gram_posDef certificateLocalRealization0gram _ hA
  intro f g hfg
  change (certificateDescendantGram2K f g : ℂ) = 0
  rw [certificateDescendantGram2K_off_type f g hfg, Int.cast_zero]

theorem certificateLocalRealization1Gram_map (t : Fin 8) :
    (certificateDescendantGram1G t).map (Int.cast : ℤ → ℂ) =
      certificateLocalDecomposition1Gram t := by
  fin_cases t <;> rfl

theorem certificateLocalRealization1size_pos (t : Fin 8) :
    0 < certificateDescendantFrames1SourceSize t := by
  fin_cases t <;> decide

/-- The checked integer Gram is exactly the full complex physical Gram. -/
theorem certificateLocalRealization1gram :
    (certificateDescendantFrames1Matrix.map (Int.cast : ℤ → ℂ))ᴴ *
        certificateDescendantFrames1Matrix.map (Int.cast : ℤ → ℂ) =
      certificateRepeatedFrameMetric certificateDescendantFrames1SourceSize
        certificateDescendantFrames1Type certificateLocalDecomposition1Gram
          (certificateDescendantGram1K.map (Int.cast : ℤ → ℂ)) := by
  have h := certificate_integer_gram_complex _ _ certificateDescendantGram1_physical
  change _ = (certificateRepeatedFrameMetric certificateDescendantFrames1SourceSize
    certificateDescendantFrames1Type certificateDescendantGram1G
      certificateDescendantGram1K).map (Int.castRingHom ℂ) at h
  rw [certificateRepeatedFrameMetric_map] at h
  simpa only [Int.coe_castRingHom, certificateLocalRealization1Gram_map] using h

/-- The scalar frame metric is positive because it comes from actual columns. -/
theorem certificateLocalRealization1scalar_posSemidef :
    (certificateDescendantGram1K.map (Int.cast : ℤ → ℂ)).PosSemidef := by
  apply certificate_scalar_metric_posSemidef_of_gram
    certificateDescendantFrames1SourceSize certificateDescendantFrames1Type
    (fun t => ⟨0, certificateLocalRealization1size_pos t⟩)
    (certificateDescendantFrames1Matrix.map (Int.cast : ℤ → ℂ))
    certificateLocalDecomposition1Gram _ certificateLocalDecomposition1Gram_posDef
    certificateLocalRealization1gram
  intro f g hfg
  change (certificateDescendantGram1K f g : ℂ) = 0
  rw [certificateDescendantGram1K_off_type f g hfg, Int.cast_zero]

/-- Any original-metric positive local block tuple constructs a positive physical operator. -/
theorem certificateLocalRealization1_exists
    (A : (t : Fin 8) → Matrix (Fin (certificateDescendantFrames1SourceSize t))
      (Fin (certificateDescendantFrames1SourceSize t)) ℂ)
    (hA : ∀ t, (certificateLocalDecomposition1Gram t * A t).PosSemidef) :
    ∃ M : Matrix CertificateLocalWord CertificateLocalWord ℂ, M.PosSemidef ∧
      M * certificateDescendantFrames1Matrix.map (Int.cast : ℤ → ℂ) =
        certificateDescendantFrames1Matrix.map (Int.cast : ℤ → ℂ) *
          Matrix.blockDiagonal' (fun f => A (certificateDescendantFrames1Type f)) := by
  apply certificate_exists_positive_frame_realization
    certificateDescendantFrames1SourceSize certificateDescendantFrames1Type
    (fun t => ⟨0, certificateLocalRealization1size_pos t⟩)
    (certificateDescendantFrames1Matrix.map (Int.cast : ℤ → ℂ))
    certificateLocalDecomposition1Gram A
    (certificateDescendantGram1K.map (Int.cast : ℤ → ℂ))
    certificateDescendantFrames1Matrix_complex_bijective
    certificateLocalDecomposition1Gram_posDef certificateLocalRealization1gram _ hA
  intro f g hfg
  change (certificateDescendantGram1K f g : ℂ) = 0
  rw [certificateDescendantGram1K_off_type f g hfg, Int.cast_zero]

theorem certificateLocalRealization2Gram_map (t : Fin 7) :
    (certificateDescendantGram2G t).map (Int.cast : ℤ → ℂ) =
      certificateLocalDecomposition2Gram t := by
  fin_cases t <;> rfl

theorem certificateLocalRealization2size_pos (t : Fin 7) :
    0 < certificateDescendantFrames2SourceSize t := by
  fin_cases t <;> decide

/-- The checked integer Gram is exactly the full complex physical Gram. -/
theorem certificateLocalRealization2gram :
    (certificateDescendantFrames2Matrix.map (Int.cast : ℤ → ℂ))ᴴ *
        certificateDescendantFrames2Matrix.map (Int.cast : ℤ → ℂ) =
      certificateRepeatedFrameMetric certificateDescendantFrames2SourceSize
        certificateDescendantFrames2Type certificateLocalDecomposition2Gram
          (certificateDescendantGram2K.map (Int.cast : ℤ → ℂ)) := by
  have h := certificate_integer_gram_complex _ _ certificateDescendantGram2_physical
  change _ = (certificateRepeatedFrameMetric certificateDescendantFrames2SourceSize
    certificateDescendantFrames2Type certificateDescendantGram2G
      certificateDescendantGram2K).map (Int.castRingHom ℂ) at h
  rw [certificateRepeatedFrameMetric_map] at h
  simpa only [Int.coe_castRingHom, certificateLocalRealization2Gram_map] using h

/-- The scalar frame metric is positive because it comes from actual columns. -/
theorem certificateLocalRealization2scalar_posSemidef :
    (certificateDescendantGram2K.map (Int.cast : ℤ → ℂ)).PosSemidef := by
  apply certificate_scalar_metric_posSemidef_of_gram
    certificateDescendantFrames2SourceSize certificateDescendantFrames2Type
    (fun t => ⟨0, certificateLocalRealization2size_pos t⟩)
    (certificateDescendantFrames2Matrix.map (Int.cast : ℤ → ℂ))
    certificateLocalDecomposition2Gram _ certificateLocalDecomposition2Gram_posDef
    certificateLocalRealization2gram
  intro f g hfg
  change (certificateDescendantGram2K f g : ℂ) = 0
  rw [certificateDescendantGram2K_off_type f g hfg, Int.cast_zero]

/-- Any original-metric positive local block tuple constructs a positive physical operator. -/
theorem certificateLocalRealization2_exists
    (A : (t : Fin 7) → Matrix (Fin (certificateDescendantFrames2SourceSize t))
      (Fin (certificateDescendantFrames2SourceSize t)) ℂ)
    (hA : ∀ t, (certificateLocalDecomposition2Gram t * A t).PosSemidef) :
    ∃ M : Matrix CertificateLocalWord CertificateLocalWord ℂ, M.PosSemidef ∧
      M * certificateDescendantFrames2Matrix.map (Int.cast : ℤ → ℂ) =
        certificateDescendantFrames2Matrix.map (Int.cast : ℤ → ℂ) *
          Matrix.blockDiagonal' (fun f => A (certificateDescendantFrames2Type f)) := by
  apply certificate_exists_positive_frame_realization
    certificateDescendantFrames2SourceSize certificateDescendantFrames2Type
    (fun t => ⟨0, certificateLocalRealization2size_pos t⟩)
    (certificateDescendantFrames2Matrix.map (Int.cast : ℤ → ℂ))
    certificateLocalDecomposition2Gram A
    (certificateDescendantGram2K.map (Int.cast : ℤ → ℂ))
    certificateDescendantFrames2Matrix_complex_bijective
    certificateLocalDecomposition2Gram_posDef certificateLocalRealization2gram _ hA
  intro f g hfg
  change (certificateDescendantGram2K f g : ℂ) = 0
  rw [certificateDescendantGram2K_off_type f g hfg, Int.cast_zero]

end ThreeCopyQutritWerner
