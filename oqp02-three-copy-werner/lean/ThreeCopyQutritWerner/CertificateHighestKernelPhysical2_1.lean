module

public import ThreeCopyQutritWerner.CertificateHighestKernelChecks2_1
public import ThreeCopyQutritWerner.CertificateHighestKernelPhysical

@[expose] public section


/-! Exact physical highest space and recovered operator action for one original frame.
All finite reconstruction premises are discharged by the source-bound checks. -/

noncomputable section

open scoped BigOperators Matrix ComplexOrder

namespace ThreeCopyQutritWerner

theorem certificateHighestKernel2_1columns_highest (j : Fin 4) :
    certificateIsHighest {0} certificateHighestKernel2_1Weight (fun w => (certificateLocalFrame2_1 w j : ℂ)) :=
  certificateIntFrame_columns_highest {0} certificateHighestKernel2_1Weight certificateLocalFrame2_1
    certificateLocalFrame2_1_weight certificateLocalFrame2_1_raising01 certificateLocalFrame2_1_raising12 j

/-- Every physical highest vector has the original, explicitly reconstructed coefficients. -/
theorem certificateHighestKernel2_1highest_reconstruct (v : CertificateLocalWord → ℂ)
    (hv : certificateIsHighest {0} certificateHighestKernel2_1Weight v) :
    v = (certificateLocalFrame2_1.map (Int.cast : ℤ → ℂ)) *ᵥ
      (certificateHighestKernel2_1P.map (Int.cast : ℤ → ℂ) *ᵥ (v ∘ certificateHighestKernel2_1Rows)) := by
  have hR : certificateHighestKernel2_1R = certificateRestrictedRaising {0} certificateHighestKernel2_1Rows certificateHighestKernel2_1Tests := by
    ext a c
    rw [certificateHighestKernel2_1R_bound]
    by_cases h : (certificateHighestKernel2_1Tests a).1 = 0 <;> simp [certificateRestrictedRaising, h]
  exact certificateHighestPhysical_reconstruct {0} certificateHighestKernel2_1Weight certificateLocalFrame2_1
    certificateHighestKernel2_1columns_highest certificateHighestKernel2_1Rows certificateHighestKernel2_1Rows_injective
    certificateHighestKernel2_1Rows_cover certificateHighestKernel2_1Tests certificateHighestKernel2_1U certificateHighestKernel2_1P certificateHighestKernel2_1R certificateHighestKernel2_1W
    certificateHighestKernel2_1U_bound hR certificateHighestKernel2_1denominator certificateHighestKernel2_1denominator_ne_zero
    certificateHighestKernel2_1reconstruction v hv

/-- The actual physical highest-vector space equals the range of this original frame. -/
theorem certificateHighestKernel2_1highest_iff_range (v : CertificateLocalWord → ℂ) :
    certificateIsHighest {0} certificateHighestKernel2_1Weight v ↔
      ∃ a : Fin 4 → ℂ, (certificateLocalFrame2_1.map (Int.cast : ℤ → ℂ)) *ᵥ a = v := by
  constructor
  · intro hv
    exact ⟨certificateHighestKernel2_1P.map (Int.cast : ℤ → ℂ) *ᵥ (v ∘ certificateHighestKernel2_1Rows),
      (certificateHighestKernel2_1highest_reconstruct v hv).symm⟩
  · rintro ⟨a, rfl⟩
    exact certificateHighestPhysical_mulVec {0} certificateHighestKernel2_1Weight _ certificateHighestKernel2_1columns_highest a

/-- Generator commutation determines source action; no action premise remains. -/
theorem certificateHighestKernel2_1source_action
    (M : Matrix CertificateLocalWord CertificateLocalWord ℂ)
    (hcomm : ∀ i j : Fin 3, M * (certificateLocalGenerator {0} i j).map (Int.cast : ℤ → ℂ) =
      (certificateLocalGenerator {0} i j).map (Int.cast : ℤ → ℂ) * M) :
    M * (certificateLocalFrame2_1.map (Int.cast : ℤ → ℂ)) = (certificateLocalFrame2_1.map (Int.cast : ℤ → ℂ)) *
      (certificateHighestKernel2_1P.map (Int.cast : ℤ → ℂ) * (M * (certificateLocalFrame2_1.map (Int.cast : ℤ → ℂ))).submatrix certificateHighestKernel2_1Rows id) :=
  certificateHighestPhysical_source_action {0} certificateHighestKernel2_1Weight _ certificateHighestKernel2_1Rows
    (certificateHighestKernel2_1P.map (Int.cast : ℤ → ℂ)) certificateHighestKernel2_1columns_highest
    certificateHighestKernel2_1highest_reconstruct M hcomm

/-- The action uses the archive original Gram metric and actual physical compression. -/
theorem certificateHighestKernel2_1weighted_action
    (M : Matrix CertificateLocalWord CertificateLocalWord ℂ)
    (hcomm : ∀ i j : Fin 3, M * (certificateLocalGenerator {0} i j).map (Int.cast : ℤ → ℂ) =
      (certificateLocalGenerator {0} i j).map (Int.cast : ℤ → ℂ) * M) :
    M * (certificateLocalFrame2_1.map (Int.cast : ℤ → ℂ)) = (certificateLocalFrame2_1.map (Int.cast : ℤ → ℂ)) *
      ((certificateLocalGram2_1.map (Int.cast : ℤ → ℂ))⁻¹ * ((certificateLocalFrame2_1.map (Int.cast : ℤ → ℂ))ᴴ * M * (certificateLocalFrame2_1.map (Int.cast : ℤ → ℂ)))) := by
  have hgram : (certificateLocalFrame2_1.map (Int.cast : ℤ → ℂ))ᴴ * (certificateLocalFrame2_1.map (Int.cast : ℤ → ℂ)) = certificateLocalGram2_1.map (Int.cast : ℤ → ℂ) := by
    rw [certificateIntGram_cast_complex, certificateLocalGram2_1_correct]
  have hpos : ((certificateLocalFrame2_1.map (Int.cast : ℤ → ℂ))ᴴ * (certificateLocalFrame2_1.map (Int.cast : ℤ → ℂ))).PosDef := by
    rw [hgram]
    exact certificateLocalGram2_1_posDef
  have h := certificateHighestPhysical_weighted_action (certificateLocalFrame2_1.map (Int.cast : ℤ → ℂ)) M _
    (certificateHighestKernel2_1source_action M hcomm) hpos
  rwa [hgram] at h

/-- Unconditional recovered source action for every complex physical diagram combination. -/
theorem certificateHighestKernel2_1diagram_action (weight : Equiv.Perm (Fin 6) → ℂ) :
    certificateLocalDiagramCombination {1, 2, 3, 4, 5} weight * (certificateLocalFrame2_1.map (Int.cast : ℤ → ℂ)) = (certificateLocalFrame2_1.map (Int.cast : ℤ → ℂ)) *
      ((certificateLocalGram2_1.map (Int.cast : ℤ → ℂ))⁻¹ *
        ((certificateLocalFrame2_1.map (Int.cast : ℤ → ℂ))ᴴ * certificateLocalDiagramCombination {1, 2, 3, 4, 5} weight * (certificateLocalFrame2_1.map (Int.cast : ℤ → ℂ)))) := by
  apply certificateHighestKernel2_1weighted_action
  intro i j
  apply certificateDiagramCombination_commutes_of_each
  intro σ
  have h : ({1, 2, 3, 4, 5} : Finset (Fin 6))ᶜ = {0} := by decide
  simpa only [h] using certificateLocalDiagram_generator_complex {1, 2, 3, 4, 5} σ i j

end ThreeCopyQutritWerner
