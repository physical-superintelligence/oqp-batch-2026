module

public import ThreeCopyQutritWerner.CertificateHighestKernelChecks1_6
public import ThreeCopyQutritWerner.CertificateHighestKernelPhysical

@[expose] public section


/-! Exact physical highest space and recovered operator action for one original frame.
All finite reconstruction premises are discharged by the source-bound checks. -/

noncomputable section

open scoped BigOperators Matrix ComplexOrder

namespace ThreeCopyQutritWerner

theorem certificateHighestKernel1_6columns_highest (j : Fin 17) :
    certificateIsHighest {0, 1, 2} certificateHighestKernel1_6Weight (fun w => (certificateLocalFrame1_6 w j : ℂ)) :=
  certificateIntFrame_columns_highest {0, 1, 2} certificateHighestKernel1_6Weight certificateLocalFrame1_6
    certificateLocalFrame1_6_weight certificateLocalFrame1_6_raising01 certificateLocalFrame1_6_raising12 j

/-- Every physical highest vector has the original, explicitly reconstructed coefficients. -/
theorem certificateHighestKernel1_6highest_reconstruct (v : CertificateLocalWord → ℂ)
    (hv : certificateIsHighest {0, 1, 2} certificateHighestKernel1_6Weight v) :
    v = (certificateLocalFrame1_6.map (Int.cast : ℤ → ℂ)) *ᵥ
      (certificateHighestKernel1_6P.map (Int.cast : ℤ → ℂ) *ᵥ (v ∘ certificateHighestKernel1_6Rows)) := by
  have hR : certificateHighestKernel1_6R = certificateRestrictedRaising {0, 1, 2} certificateHighestKernel1_6Rows certificateHighestKernel1_6Tests := by
    ext a c
    rw [certificateHighestKernel1_6R_bound]
    by_cases h : (certificateHighestKernel1_6Tests a).1 = 0 <;> simp [certificateRestrictedRaising, h]
  exact certificateHighestPhysical_reconstruct {0, 1, 2} certificateHighestKernel1_6Weight certificateLocalFrame1_6
    certificateHighestKernel1_6columns_highest certificateHighestKernel1_6Rows certificateHighestKernel1_6Rows_injective
    certificateHighestKernel1_6Rows_cover certificateHighestKernel1_6Tests certificateHighestKernel1_6U certificateHighestKernel1_6P certificateHighestKernel1_6R certificateHighestKernel1_6W
    certificateHighestKernel1_6U_bound hR certificateHighestKernel1_6denominator certificateHighestKernel1_6denominator_ne_zero
    certificateHighestKernel1_6reconstruction v hv

/-- The actual physical highest-vector space equals the range of this original frame. -/
theorem certificateHighestKernel1_6highest_iff_range (v : CertificateLocalWord → ℂ) :
    certificateIsHighest {0, 1, 2} certificateHighestKernel1_6Weight v ↔
      ∃ a : Fin 17 → ℂ, (certificateLocalFrame1_6.map (Int.cast : ℤ → ℂ)) *ᵥ a = v := by
  constructor
  · intro hv
    exact ⟨certificateHighestKernel1_6P.map (Int.cast : ℤ → ℂ) *ᵥ (v ∘ certificateHighestKernel1_6Rows),
      (certificateHighestKernel1_6highest_reconstruct v hv).symm⟩
  · rintro ⟨a, rfl⟩
    exact certificateHighestPhysical_mulVec {0, 1, 2} certificateHighestKernel1_6Weight _ certificateHighestKernel1_6columns_highest a

/-- Generator commutation determines source action; no action premise remains. -/
theorem certificateHighestKernel1_6source_action
    (M : Matrix CertificateLocalWord CertificateLocalWord ℂ)
    (hcomm : ∀ i j : Fin 3, M * (certificateLocalGenerator {0, 1, 2} i j).map (Int.cast : ℤ → ℂ) =
      (certificateLocalGenerator {0, 1, 2} i j).map (Int.cast : ℤ → ℂ) * M) :
    M * (certificateLocalFrame1_6.map (Int.cast : ℤ → ℂ)) = (certificateLocalFrame1_6.map (Int.cast : ℤ → ℂ)) *
      (certificateHighestKernel1_6P.map (Int.cast : ℤ → ℂ) * (M * (certificateLocalFrame1_6.map (Int.cast : ℤ → ℂ))).submatrix certificateHighestKernel1_6Rows id) :=
  certificateHighestPhysical_source_action {0, 1, 2} certificateHighestKernel1_6Weight _ certificateHighestKernel1_6Rows
    (certificateHighestKernel1_6P.map (Int.cast : ℤ → ℂ)) certificateHighestKernel1_6columns_highest
    certificateHighestKernel1_6highest_reconstruct M hcomm

/-- The action uses the archive original Gram metric and actual physical compression. -/
theorem certificateHighestKernel1_6weighted_action
    (M : Matrix CertificateLocalWord CertificateLocalWord ℂ)
    (hcomm : ∀ i j : Fin 3, M * (certificateLocalGenerator {0, 1, 2} i j).map (Int.cast : ℤ → ℂ) =
      (certificateLocalGenerator {0, 1, 2} i j).map (Int.cast : ℤ → ℂ) * M) :
    M * (certificateLocalFrame1_6.map (Int.cast : ℤ → ℂ)) = (certificateLocalFrame1_6.map (Int.cast : ℤ → ℂ)) *
      ((certificateLocalGram1_6.map (Int.cast : ℤ → ℂ))⁻¹ * ((certificateLocalFrame1_6.map (Int.cast : ℤ → ℂ))ᴴ * M * (certificateLocalFrame1_6.map (Int.cast : ℤ → ℂ)))) := by
  have hgram : (certificateLocalFrame1_6.map (Int.cast : ℤ → ℂ))ᴴ * (certificateLocalFrame1_6.map (Int.cast : ℤ → ℂ)) = certificateLocalGram1_6.map (Int.cast : ℤ → ℂ) := by
    rw [certificateIntGram_cast_complex, certificateLocalGram1_6_correct]
  have hpos : ((certificateLocalFrame1_6.map (Int.cast : ℤ → ℂ))ᴴ * (certificateLocalFrame1_6.map (Int.cast : ℤ → ℂ))).PosDef := by
    rw [hgram]
    exact certificateLocalGram1_6_posDef
  have h := certificateHighestPhysical_weighted_action (certificateLocalFrame1_6.map (Int.cast : ℤ → ℂ)) M _
    (certificateHighestKernel1_6source_action M hcomm) hpos
  rwa [hgram] at h

/-- Unconditional recovered source action for every complex physical diagram combination. -/
theorem certificateHighestKernel1_6diagram_action (weight : Equiv.Perm (Fin 6) → ℂ) :
    certificateLocalDiagramCombination {3, 4, 5} weight * (certificateLocalFrame1_6.map (Int.cast : ℤ → ℂ)) = (certificateLocalFrame1_6.map (Int.cast : ℤ → ℂ)) *
      ((certificateLocalGram1_6.map (Int.cast : ℤ → ℂ))⁻¹ *
        ((certificateLocalFrame1_6.map (Int.cast : ℤ → ℂ))ᴴ * certificateLocalDiagramCombination {3, 4, 5} weight * (certificateLocalFrame1_6.map (Int.cast : ℤ → ℂ)))) := by
  apply certificateHighestKernel1_6weighted_action
  intro i j
  apply certificateDiagramCombination_commutes_of_each
  intro σ
  have h : ({3, 4, 5} : Finset (Fin 6))ᶜ = {0, 1, 2} := by decide
  simpa only [h] using certificateLocalDiagram_generator_complex {3, 4, 5} σ i j

end ThreeCopyQutritWerner
