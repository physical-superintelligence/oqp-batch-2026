module

public import ThreeCopyQutritWerner.CertificateHighestKernelChecks1_3
public import ThreeCopyQutritWerner.CertificateHighestKernelPhysical

@[expose] public section


/-! Exact physical highest space and recovered operator action for one original frame.
All finite reconstruction premises are discharged by the source-bound checks. -/

noncomputable section

open scoped BigOperators Matrix ComplexOrder

namespace ThreeCopyQutritWerner

theorem certificateHighestKernel1_3columns_highest (j : Fin 9) :
    certificateIsHighest {0, 1, 2} certificateHighestKernel1_3Weight (fun w => (certificateLocalFrame1_3 w j : ℂ)) :=
  certificateIntFrame_columns_highest {0, 1, 2} certificateHighestKernel1_3Weight certificateLocalFrame1_3
    certificateLocalFrame1_3_weight certificateLocalFrame1_3_raising01 certificateLocalFrame1_3_raising12 j

/-- Every physical highest vector has the original, explicitly reconstructed coefficients. -/
theorem certificateHighestKernel1_3highest_reconstruct (v : CertificateLocalWord → ℂ)
    (hv : certificateIsHighest {0, 1, 2} certificateHighestKernel1_3Weight v) :
    v = (certificateLocalFrame1_3.map (Int.cast : ℤ → ℂ)) *ᵥ
      (certificateHighestKernel1_3P.map (Int.cast : ℤ → ℂ) *ᵥ (v ∘ certificateHighestKernel1_3Rows)) := by
  have hR : certificateHighestKernel1_3R = certificateRestrictedRaising {0, 1, 2} certificateHighestKernel1_3Rows certificateHighestKernel1_3Tests := by
    ext a c
    rw [certificateHighestKernel1_3R_bound]
    by_cases h : (certificateHighestKernel1_3Tests a).1 = 0 <;> simp [certificateRestrictedRaising, h]
  exact certificateHighestPhysical_reconstruct {0, 1, 2} certificateHighestKernel1_3Weight certificateLocalFrame1_3
    certificateHighestKernel1_3columns_highest certificateHighestKernel1_3Rows certificateHighestKernel1_3Rows_injective
    certificateHighestKernel1_3Rows_cover certificateHighestKernel1_3Tests certificateHighestKernel1_3U certificateHighestKernel1_3P certificateHighestKernel1_3R certificateHighestKernel1_3W
    certificateHighestKernel1_3U_bound hR certificateHighestKernel1_3denominator certificateHighestKernel1_3denominator_ne_zero
    certificateHighestKernel1_3reconstruction v hv

/-- The actual physical highest-vector space equals the range of this original frame. -/
theorem certificateHighestKernel1_3highest_iff_range (v : CertificateLocalWord → ℂ) :
    certificateIsHighest {0, 1, 2} certificateHighestKernel1_3Weight v ↔
      ∃ a : Fin 9 → ℂ, (certificateLocalFrame1_3.map (Int.cast : ℤ → ℂ)) *ᵥ a = v := by
  constructor
  · intro hv
    exact ⟨certificateHighestKernel1_3P.map (Int.cast : ℤ → ℂ) *ᵥ (v ∘ certificateHighestKernel1_3Rows),
      (certificateHighestKernel1_3highest_reconstruct v hv).symm⟩
  · rintro ⟨a, rfl⟩
    exact certificateHighestPhysical_mulVec {0, 1, 2} certificateHighestKernel1_3Weight _ certificateHighestKernel1_3columns_highest a

/-- Generator commutation determines source action; no action premise remains. -/
theorem certificateHighestKernel1_3source_action
    (M : Matrix CertificateLocalWord CertificateLocalWord ℂ)
    (hcomm : ∀ i j : Fin 3, M * (certificateLocalGenerator {0, 1, 2} i j).map (Int.cast : ℤ → ℂ) =
      (certificateLocalGenerator {0, 1, 2} i j).map (Int.cast : ℤ → ℂ) * M) :
    M * (certificateLocalFrame1_3.map (Int.cast : ℤ → ℂ)) = (certificateLocalFrame1_3.map (Int.cast : ℤ → ℂ)) *
      (certificateHighestKernel1_3P.map (Int.cast : ℤ → ℂ) * (M * (certificateLocalFrame1_3.map (Int.cast : ℤ → ℂ))).submatrix certificateHighestKernel1_3Rows id) :=
  certificateHighestPhysical_source_action {0, 1, 2} certificateHighestKernel1_3Weight _ certificateHighestKernel1_3Rows
    (certificateHighestKernel1_3P.map (Int.cast : ℤ → ℂ)) certificateHighestKernel1_3columns_highest
    certificateHighestKernel1_3highest_reconstruct M hcomm

/-- The action uses the archive original Gram metric and actual physical compression. -/
theorem certificateHighestKernel1_3weighted_action
    (M : Matrix CertificateLocalWord CertificateLocalWord ℂ)
    (hcomm : ∀ i j : Fin 3, M * (certificateLocalGenerator {0, 1, 2} i j).map (Int.cast : ℤ → ℂ) =
      (certificateLocalGenerator {0, 1, 2} i j).map (Int.cast : ℤ → ℂ) * M) :
    M * (certificateLocalFrame1_3.map (Int.cast : ℤ → ℂ)) = (certificateLocalFrame1_3.map (Int.cast : ℤ → ℂ)) *
      ((certificateLocalGram1_3.map (Int.cast : ℤ → ℂ))⁻¹ * ((certificateLocalFrame1_3.map (Int.cast : ℤ → ℂ))ᴴ * M * (certificateLocalFrame1_3.map (Int.cast : ℤ → ℂ)))) := by
  have hgram : (certificateLocalFrame1_3.map (Int.cast : ℤ → ℂ))ᴴ * (certificateLocalFrame1_3.map (Int.cast : ℤ → ℂ)) = certificateLocalGram1_3.map (Int.cast : ℤ → ℂ) := by
    rw [certificateIntGram_cast_complex, certificateLocalGram1_3_correct]
  have hpos : ((certificateLocalFrame1_3.map (Int.cast : ℤ → ℂ))ᴴ * (certificateLocalFrame1_3.map (Int.cast : ℤ → ℂ))).PosDef := by
    rw [hgram]
    exact certificateLocalGram1_3_posDef
  have h := certificateHighestPhysical_weighted_action (certificateLocalFrame1_3.map (Int.cast : ℤ → ℂ)) M _
    (certificateHighestKernel1_3source_action M hcomm) hpos
  rwa [hgram] at h

/-- Unconditional recovered source action for every complex physical diagram combination. -/
theorem certificateHighestKernel1_3diagram_action (weight : Equiv.Perm (Fin 6) → ℂ) :
    certificateLocalDiagramCombination {3, 4, 5} weight * (certificateLocalFrame1_3.map (Int.cast : ℤ → ℂ)) = (certificateLocalFrame1_3.map (Int.cast : ℤ → ℂ)) *
      ((certificateLocalGram1_3.map (Int.cast : ℤ → ℂ))⁻¹ *
        ((certificateLocalFrame1_3.map (Int.cast : ℤ → ℂ))ᴴ * certificateLocalDiagramCombination {3, 4, 5} weight * (certificateLocalFrame1_3.map (Int.cast : ℤ → ℂ)))) := by
  apply certificateHighestKernel1_3weighted_action
  intro i j
  apply certificateDiagramCombination_commutes_of_each
  intro σ
  have h : ({3, 4, 5} : Finset (Fin 6))ᶜ = {0, 1, 2} := by decide
  simpa only [h] using certificateLocalDiagram_generator_complex {3, 4, 5} σ i j

end ThreeCopyQutritWerner
