module

public import ThreeCopyQutritWerner.CertificateHighestKernelChecks1_0
public import ThreeCopyQutritWerner.CertificateHighestKernelPhysical

@[expose] public section


/-! Exact physical highest space and recovered operator action for one original frame.
All finite reconstruction premises are discharged by the source-bound checks. -/

noncomputable section

open scoped BigOperators Matrix ComplexOrder

namespace ThreeCopyQutritWerner

theorem certificateHighestKernel1_0columns_highest (j : Fin 1) :
    certificateIsHighest {0, 1, 2} certificateHighestKernel1_0Weight (fun w => (certificateLocalFrame1_0 w j : ℂ)) :=
  certificateIntFrame_columns_highest {0, 1, 2} certificateHighestKernel1_0Weight certificateLocalFrame1_0
    certificateLocalFrame1_0_weight certificateLocalFrame1_0_raising01 certificateLocalFrame1_0_raising12 j

/-- Every physical highest vector has the original, explicitly reconstructed coefficients. -/
theorem certificateHighestKernel1_0highest_reconstruct (v : CertificateLocalWord → ℂ)
    (hv : certificateIsHighest {0, 1, 2} certificateHighestKernel1_0Weight v) :
    v = (certificateLocalFrame1_0.map (Int.cast : ℤ → ℂ)) *ᵥ
      (certificateHighestKernel1_0P.map (Int.cast : ℤ → ℂ) *ᵥ (v ∘ certificateHighestKernel1_0Rows)) := by
  have hR : certificateHighestKernel1_0R = certificateRestrictedRaising {0, 1, 2} certificateHighestKernel1_0Rows certificateHighestKernel1_0Tests := by
    ext a c
    rw [certificateHighestKernel1_0R_bound]
    by_cases h : (certificateHighestKernel1_0Tests a).1 = 0 <;> simp [certificateRestrictedRaising, h]
  exact certificateHighestPhysical_reconstruct {0, 1, 2} certificateHighestKernel1_0Weight certificateLocalFrame1_0
    certificateHighestKernel1_0columns_highest certificateHighestKernel1_0Rows certificateHighestKernel1_0Rows_injective
    certificateHighestKernel1_0Rows_cover certificateHighestKernel1_0Tests certificateHighestKernel1_0U certificateHighestKernel1_0P certificateHighestKernel1_0R certificateHighestKernel1_0W
    certificateHighestKernel1_0U_bound hR certificateHighestKernel1_0denominator certificateHighestKernel1_0denominator_ne_zero
    certificateHighestKernel1_0reconstruction v hv

/-- The actual physical highest-vector space equals the range of this original frame. -/
theorem certificateHighestKernel1_0highest_iff_range (v : CertificateLocalWord → ℂ) :
    certificateIsHighest {0, 1, 2} certificateHighestKernel1_0Weight v ↔
      ∃ a : Fin 1 → ℂ, (certificateLocalFrame1_0.map (Int.cast : ℤ → ℂ)) *ᵥ a = v := by
  constructor
  · intro hv
    exact ⟨certificateHighestKernel1_0P.map (Int.cast : ℤ → ℂ) *ᵥ (v ∘ certificateHighestKernel1_0Rows),
      (certificateHighestKernel1_0highest_reconstruct v hv).symm⟩
  · rintro ⟨a, rfl⟩
    exact certificateHighestPhysical_mulVec {0, 1, 2} certificateHighestKernel1_0Weight _ certificateHighestKernel1_0columns_highest a

/-- Generator commutation determines source action; no action premise remains. -/
theorem certificateHighestKernel1_0source_action
    (M : Matrix CertificateLocalWord CertificateLocalWord ℂ)
    (hcomm : ∀ i j : Fin 3, M * (certificateLocalGenerator {0, 1, 2} i j).map (Int.cast : ℤ → ℂ) =
      (certificateLocalGenerator {0, 1, 2} i j).map (Int.cast : ℤ → ℂ) * M) :
    M * (certificateLocalFrame1_0.map (Int.cast : ℤ → ℂ)) = (certificateLocalFrame1_0.map (Int.cast : ℤ → ℂ)) *
      (certificateHighestKernel1_0P.map (Int.cast : ℤ → ℂ) * (M * (certificateLocalFrame1_0.map (Int.cast : ℤ → ℂ))).submatrix certificateHighestKernel1_0Rows id) :=
  certificateHighestPhysical_source_action {0, 1, 2} certificateHighestKernel1_0Weight _ certificateHighestKernel1_0Rows
    (certificateHighestKernel1_0P.map (Int.cast : ℤ → ℂ)) certificateHighestKernel1_0columns_highest
    certificateHighestKernel1_0highest_reconstruct M hcomm

/-- The action uses the archive original Gram metric and actual physical compression. -/
theorem certificateHighestKernel1_0weighted_action
    (M : Matrix CertificateLocalWord CertificateLocalWord ℂ)
    (hcomm : ∀ i j : Fin 3, M * (certificateLocalGenerator {0, 1, 2} i j).map (Int.cast : ℤ → ℂ) =
      (certificateLocalGenerator {0, 1, 2} i j).map (Int.cast : ℤ → ℂ) * M) :
    M * (certificateLocalFrame1_0.map (Int.cast : ℤ → ℂ)) = (certificateLocalFrame1_0.map (Int.cast : ℤ → ℂ)) *
      ((certificateLocalGram1_0.map (Int.cast : ℤ → ℂ))⁻¹ * ((certificateLocalFrame1_0.map (Int.cast : ℤ → ℂ))ᴴ * M * (certificateLocalFrame1_0.map (Int.cast : ℤ → ℂ)))) := by
  have hgram : (certificateLocalFrame1_0.map (Int.cast : ℤ → ℂ))ᴴ * (certificateLocalFrame1_0.map (Int.cast : ℤ → ℂ)) = certificateLocalGram1_0.map (Int.cast : ℤ → ℂ) := by
    rw [certificateIntGram_cast_complex, certificateLocalGram1_0_correct]
  have hpos : ((certificateLocalFrame1_0.map (Int.cast : ℤ → ℂ))ᴴ * (certificateLocalFrame1_0.map (Int.cast : ℤ → ℂ))).PosDef := by
    rw [hgram]
    exact certificateLocalGram1_0_posDef
  have h := certificateHighestPhysical_weighted_action (certificateLocalFrame1_0.map (Int.cast : ℤ → ℂ)) M _
    (certificateHighestKernel1_0source_action M hcomm) hpos
  rwa [hgram] at h

/-- Unconditional recovered source action for every complex physical diagram combination. -/
theorem certificateHighestKernel1_0diagram_action (weight : Equiv.Perm (Fin 6) → ℂ) :
    certificateLocalDiagramCombination {3, 4, 5} weight * (certificateLocalFrame1_0.map (Int.cast : ℤ → ℂ)) = (certificateLocalFrame1_0.map (Int.cast : ℤ → ℂ)) *
      ((certificateLocalGram1_0.map (Int.cast : ℤ → ℂ))⁻¹ *
        ((certificateLocalFrame1_0.map (Int.cast : ℤ → ℂ))ᴴ * certificateLocalDiagramCombination {3, 4, 5} weight * (certificateLocalFrame1_0.map (Int.cast : ℤ → ℂ)))) := by
  apply certificateHighestKernel1_0weighted_action
  intro i j
  apply certificateDiagramCombination_commutes_of_each
  intro σ
  have h : ({3, 4, 5} : Finset (Fin 6))ᶜ = {0, 1, 2} := by decide
  simpa only [h] using certificateLocalDiagram_generator_complex {3, 4, 5} σ i j

end ThreeCopyQutritWerner
