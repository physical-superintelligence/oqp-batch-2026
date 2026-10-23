module

public import ThreeCopyQutritWerner.CertificateHighestKernelChecks1_1
public import ThreeCopyQutritWerner.CertificateHighestKernelPhysical

@[expose] public section


/-! Exact physical highest space and recovered operator action for one original frame.
All finite reconstruction premises are discharged by the source-bound checks. -/

noncomputable section

open scoped BigOperators Matrix ComplexOrder

namespace ThreeCopyQutritWerner

theorem certificateHighestKernel1_1columns_highest (j : Fin 2) :
    certificateIsHighest {0, 1, 2} certificateHighestKernel1_1Weight (fun w => (certificateLocalFrame1_1 w j : ℂ)) :=
  certificateIntFrame_columns_highest {0, 1, 2} certificateHighestKernel1_1Weight certificateLocalFrame1_1
    certificateLocalFrame1_1_weight certificateLocalFrame1_1_raising01 certificateLocalFrame1_1_raising12 j

/-- Every physical highest vector has the original, explicitly reconstructed coefficients. -/
theorem certificateHighestKernel1_1highest_reconstruct (v : CertificateLocalWord → ℂ)
    (hv : certificateIsHighest {0, 1, 2} certificateHighestKernel1_1Weight v) :
    v = (certificateLocalFrame1_1.map (Int.cast : ℤ → ℂ)) *ᵥ
      (certificateHighestKernel1_1P.map (Int.cast : ℤ → ℂ) *ᵥ (v ∘ certificateHighestKernel1_1Rows)) := by
  have hR : certificateHighestKernel1_1R = certificateRestrictedRaising {0, 1, 2} certificateHighestKernel1_1Rows certificateHighestKernel1_1Tests := by
    ext a c
    rw [certificateHighestKernel1_1R_bound]
    by_cases h : (certificateHighestKernel1_1Tests a).1 = 0 <;> simp [certificateRestrictedRaising, h]
  exact certificateHighestPhysical_reconstruct {0, 1, 2} certificateHighestKernel1_1Weight certificateLocalFrame1_1
    certificateHighestKernel1_1columns_highest certificateHighestKernel1_1Rows certificateHighestKernel1_1Rows_injective
    certificateHighestKernel1_1Rows_cover certificateHighestKernel1_1Tests certificateHighestKernel1_1U certificateHighestKernel1_1P certificateHighestKernel1_1R certificateHighestKernel1_1W
    certificateHighestKernel1_1U_bound hR certificateHighestKernel1_1denominator certificateHighestKernel1_1denominator_ne_zero
    certificateHighestKernel1_1reconstruction v hv

/-- The actual physical highest-vector space equals the range of this original frame. -/
theorem certificateHighestKernel1_1highest_iff_range (v : CertificateLocalWord → ℂ) :
    certificateIsHighest {0, 1, 2} certificateHighestKernel1_1Weight v ↔
      ∃ a : Fin 2 → ℂ, (certificateLocalFrame1_1.map (Int.cast : ℤ → ℂ)) *ᵥ a = v := by
  constructor
  · intro hv
    exact ⟨certificateHighestKernel1_1P.map (Int.cast : ℤ → ℂ) *ᵥ (v ∘ certificateHighestKernel1_1Rows),
      (certificateHighestKernel1_1highest_reconstruct v hv).symm⟩
  · rintro ⟨a, rfl⟩
    exact certificateHighestPhysical_mulVec {0, 1, 2} certificateHighestKernel1_1Weight _ certificateHighestKernel1_1columns_highest a

/-- Generator commutation determines source action; no action premise remains. -/
theorem certificateHighestKernel1_1source_action
    (M : Matrix CertificateLocalWord CertificateLocalWord ℂ)
    (hcomm : ∀ i j : Fin 3, M * (certificateLocalGenerator {0, 1, 2} i j).map (Int.cast : ℤ → ℂ) =
      (certificateLocalGenerator {0, 1, 2} i j).map (Int.cast : ℤ → ℂ) * M) :
    M * (certificateLocalFrame1_1.map (Int.cast : ℤ → ℂ)) = (certificateLocalFrame1_1.map (Int.cast : ℤ → ℂ)) *
      (certificateHighestKernel1_1P.map (Int.cast : ℤ → ℂ) * (M * (certificateLocalFrame1_1.map (Int.cast : ℤ → ℂ))).submatrix certificateHighestKernel1_1Rows id) :=
  certificateHighestPhysical_source_action {0, 1, 2} certificateHighestKernel1_1Weight _ certificateHighestKernel1_1Rows
    (certificateHighestKernel1_1P.map (Int.cast : ℤ → ℂ)) certificateHighestKernel1_1columns_highest
    certificateHighestKernel1_1highest_reconstruct M hcomm

/-- The action uses the archive original Gram metric and actual physical compression. -/
theorem certificateHighestKernel1_1weighted_action
    (M : Matrix CertificateLocalWord CertificateLocalWord ℂ)
    (hcomm : ∀ i j : Fin 3, M * (certificateLocalGenerator {0, 1, 2} i j).map (Int.cast : ℤ → ℂ) =
      (certificateLocalGenerator {0, 1, 2} i j).map (Int.cast : ℤ → ℂ) * M) :
    M * (certificateLocalFrame1_1.map (Int.cast : ℤ → ℂ)) = (certificateLocalFrame1_1.map (Int.cast : ℤ → ℂ)) *
      ((certificateLocalGram1_1.map (Int.cast : ℤ → ℂ))⁻¹ * ((certificateLocalFrame1_1.map (Int.cast : ℤ → ℂ))ᴴ * M * (certificateLocalFrame1_1.map (Int.cast : ℤ → ℂ)))) := by
  have hgram : (certificateLocalFrame1_1.map (Int.cast : ℤ → ℂ))ᴴ * (certificateLocalFrame1_1.map (Int.cast : ℤ → ℂ)) = certificateLocalGram1_1.map (Int.cast : ℤ → ℂ) := by
    rw [certificateIntGram_cast_complex, certificateLocalGram1_1_correct]
  have hpos : ((certificateLocalFrame1_1.map (Int.cast : ℤ → ℂ))ᴴ * (certificateLocalFrame1_1.map (Int.cast : ℤ → ℂ))).PosDef := by
    rw [hgram]
    exact certificateLocalGram1_1_posDef
  have h := certificateHighestPhysical_weighted_action (certificateLocalFrame1_1.map (Int.cast : ℤ → ℂ)) M _
    (certificateHighestKernel1_1source_action M hcomm) hpos
  rwa [hgram] at h

/-- Unconditional recovered source action for every complex physical diagram combination. -/
theorem certificateHighestKernel1_1diagram_action (weight : Equiv.Perm (Fin 6) → ℂ) :
    certificateLocalDiagramCombination {3, 4, 5} weight * (certificateLocalFrame1_1.map (Int.cast : ℤ → ℂ)) = (certificateLocalFrame1_1.map (Int.cast : ℤ → ℂ)) *
      ((certificateLocalGram1_1.map (Int.cast : ℤ → ℂ))⁻¹ *
        ((certificateLocalFrame1_1.map (Int.cast : ℤ → ℂ))ᴴ * certificateLocalDiagramCombination {3, 4, 5} weight * (certificateLocalFrame1_1.map (Int.cast : ℤ → ℂ)))) := by
  apply certificateHighestKernel1_1weighted_action
  intro i j
  apply certificateDiagramCombination_commutes_of_each
  intro σ
  have h : ({3, 4, 5} : Finset (Fin 6))ᶜ = {0, 1, 2} := by decide
  simpa only [h] using certificateLocalDiagram_generator_complex {3, 4, 5} σ i j

end ThreeCopyQutritWerner
