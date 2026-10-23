module

public import ThreeCopyQutritWerner.CertificateHighestKernelChecks1_4
public import ThreeCopyQutritWerner.CertificateHighestKernelPhysical

@[expose] public section


/-! Exact physical highest space and recovered operator action for one original frame.
All finite reconstruction premises are discharged by the source-bound checks. -/

noncomputable section

open scoped BigOperators Matrix ComplexOrder

namespace ThreeCopyQutritWerner

theorem certificateHighestKernel1_4columns_highest (j : Fin 7) :
    certificateIsHighest {0, 1, 2} certificateHighestKernel1_4Weight (fun w => (certificateLocalFrame1_4 w j : ℂ)) :=
  certificateIntFrame_columns_highest {0, 1, 2} certificateHighestKernel1_4Weight certificateLocalFrame1_4
    certificateLocalFrame1_4_weight certificateLocalFrame1_4_raising01 certificateLocalFrame1_4_raising12 j

/-- Every physical highest vector has the original, explicitly reconstructed coefficients. -/
theorem certificateHighestKernel1_4highest_reconstruct (v : CertificateLocalWord → ℂ)
    (hv : certificateIsHighest {0, 1, 2} certificateHighestKernel1_4Weight v) :
    v = (certificateLocalFrame1_4.map (Int.cast : ℤ → ℂ)) *ᵥ
      (certificateHighestKernel1_4P.map (Int.cast : ℤ → ℂ) *ᵥ (v ∘ certificateHighestKernel1_4Rows)) := by
  have hR : certificateHighestKernel1_4R = certificateRestrictedRaising {0, 1, 2} certificateHighestKernel1_4Rows certificateHighestKernel1_4Tests := by
    ext a c
    rw [certificateHighestKernel1_4R_bound]
    by_cases h : (certificateHighestKernel1_4Tests a).1 = 0 <;> simp [certificateRestrictedRaising, h]
  exact certificateHighestPhysical_reconstruct {0, 1, 2} certificateHighestKernel1_4Weight certificateLocalFrame1_4
    certificateHighestKernel1_4columns_highest certificateHighestKernel1_4Rows certificateHighestKernel1_4Rows_injective
    certificateHighestKernel1_4Rows_cover certificateHighestKernel1_4Tests certificateHighestKernel1_4U certificateHighestKernel1_4P certificateHighestKernel1_4R certificateHighestKernel1_4W
    certificateHighestKernel1_4U_bound hR certificateHighestKernel1_4denominator certificateHighestKernel1_4denominator_ne_zero
    certificateHighestKernel1_4reconstruction v hv

/-- The actual physical highest-vector space equals the range of this original frame. -/
theorem certificateHighestKernel1_4highest_iff_range (v : CertificateLocalWord → ℂ) :
    certificateIsHighest {0, 1, 2} certificateHighestKernel1_4Weight v ↔
      ∃ a : Fin 7 → ℂ, (certificateLocalFrame1_4.map (Int.cast : ℤ → ℂ)) *ᵥ a = v := by
  constructor
  · intro hv
    exact ⟨certificateHighestKernel1_4P.map (Int.cast : ℤ → ℂ) *ᵥ (v ∘ certificateHighestKernel1_4Rows),
      (certificateHighestKernel1_4highest_reconstruct v hv).symm⟩
  · rintro ⟨a, rfl⟩
    exact certificateHighestPhysical_mulVec {0, 1, 2} certificateHighestKernel1_4Weight _ certificateHighestKernel1_4columns_highest a

/-- Generator commutation determines source action; no action premise remains. -/
theorem certificateHighestKernel1_4source_action
    (M : Matrix CertificateLocalWord CertificateLocalWord ℂ)
    (hcomm : ∀ i j : Fin 3, M * (certificateLocalGenerator {0, 1, 2} i j).map (Int.cast : ℤ → ℂ) =
      (certificateLocalGenerator {0, 1, 2} i j).map (Int.cast : ℤ → ℂ) * M) :
    M * (certificateLocalFrame1_4.map (Int.cast : ℤ → ℂ)) = (certificateLocalFrame1_4.map (Int.cast : ℤ → ℂ)) *
      (certificateHighestKernel1_4P.map (Int.cast : ℤ → ℂ) * (M * (certificateLocalFrame1_4.map (Int.cast : ℤ → ℂ))).submatrix certificateHighestKernel1_4Rows id) :=
  certificateHighestPhysical_source_action {0, 1, 2} certificateHighestKernel1_4Weight _ certificateHighestKernel1_4Rows
    (certificateHighestKernel1_4P.map (Int.cast : ℤ → ℂ)) certificateHighestKernel1_4columns_highest
    certificateHighestKernel1_4highest_reconstruct M hcomm

/-- The action uses the archive original Gram metric and actual physical compression. -/
theorem certificateHighestKernel1_4weighted_action
    (M : Matrix CertificateLocalWord CertificateLocalWord ℂ)
    (hcomm : ∀ i j : Fin 3, M * (certificateLocalGenerator {0, 1, 2} i j).map (Int.cast : ℤ → ℂ) =
      (certificateLocalGenerator {0, 1, 2} i j).map (Int.cast : ℤ → ℂ) * M) :
    M * (certificateLocalFrame1_4.map (Int.cast : ℤ → ℂ)) = (certificateLocalFrame1_4.map (Int.cast : ℤ → ℂ)) *
      ((certificateLocalGram1_4.map (Int.cast : ℤ → ℂ))⁻¹ * ((certificateLocalFrame1_4.map (Int.cast : ℤ → ℂ))ᴴ * M * (certificateLocalFrame1_4.map (Int.cast : ℤ → ℂ)))) := by
  have hgram : (certificateLocalFrame1_4.map (Int.cast : ℤ → ℂ))ᴴ * (certificateLocalFrame1_4.map (Int.cast : ℤ → ℂ)) = certificateLocalGram1_4.map (Int.cast : ℤ → ℂ) := by
    rw [certificateIntGram_cast_complex, certificateLocalGram1_4_correct]
  have hpos : ((certificateLocalFrame1_4.map (Int.cast : ℤ → ℂ))ᴴ * (certificateLocalFrame1_4.map (Int.cast : ℤ → ℂ))).PosDef := by
    rw [hgram]
    exact certificateLocalGram1_4_posDef
  have h := certificateHighestPhysical_weighted_action (certificateLocalFrame1_4.map (Int.cast : ℤ → ℂ)) M _
    (certificateHighestKernel1_4source_action M hcomm) hpos
  rwa [hgram] at h

/-- Unconditional recovered source action for every complex physical diagram combination. -/
theorem certificateHighestKernel1_4diagram_action (weight : Equiv.Perm (Fin 6) → ℂ) :
    certificateLocalDiagramCombination {3, 4, 5} weight * (certificateLocalFrame1_4.map (Int.cast : ℤ → ℂ)) = (certificateLocalFrame1_4.map (Int.cast : ℤ → ℂ)) *
      ((certificateLocalGram1_4.map (Int.cast : ℤ → ℂ))⁻¹ *
        ((certificateLocalFrame1_4.map (Int.cast : ℤ → ℂ))ᴴ * certificateLocalDiagramCombination {3, 4, 5} weight * (certificateLocalFrame1_4.map (Int.cast : ℤ → ℂ)))) := by
  apply certificateHighestKernel1_4weighted_action
  intro i j
  apply certificateDiagramCombination_commutes_of_each
  intro σ
  have h : ({3, 4, 5} : Finset (Fin 6))ᶜ = {0, 1, 2} := by decide
  simpa only [h] using certificateLocalDiagram_generator_complex {3, 4, 5} σ i j

end ThreeCopyQutritWerner
