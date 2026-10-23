module

public import ThreeCopyQutritWerner.CertificateHighestKernelChecks1_7
public import ThreeCopyQutritWerner.CertificateHighestKernelPhysical

@[expose] public section


/-! Exact physical highest space and recovered operator action for one original frame.
All finite reconstruction premises are discharged by the source-bound checks. -/

noncomputable section

open scoped BigOperators Matrix ComplexOrder

namespace ThreeCopyQutritWerner

theorem certificateHighestKernel1_7columns_highest (j : Fin 6) :
    certificateIsHighest {0, 1, 2} certificateHighestKernel1_7Weight (fun w => (certificateLocalFrame1_7 w j : ℂ)) :=
  certificateIntFrame_columns_highest {0, 1, 2} certificateHighestKernel1_7Weight certificateLocalFrame1_7
    certificateLocalFrame1_7_weight certificateLocalFrame1_7_raising01 certificateLocalFrame1_7_raising12 j

/-- Every physical highest vector has the original, explicitly reconstructed coefficients. -/
theorem certificateHighestKernel1_7highest_reconstruct (v : CertificateLocalWord → ℂ)
    (hv : certificateIsHighest {0, 1, 2} certificateHighestKernel1_7Weight v) :
    v = (certificateLocalFrame1_7.map (Int.cast : ℤ → ℂ)) *ᵥ
      (certificateHighestKernel1_7P.map (Int.cast : ℤ → ℂ) *ᵥ (v ∘ certificateHighestKernel1_7Rows)) := by
  have hR : certificateHighestKernel1_7R = certificateRestrictedRaising {0, 1, 2} certificateHighestKernel1_7Rows certificateHighestKernel1_7Tests := by
    ext a c
    rw [certificateHighestKernel1_7R_bound]
    by_cases h : (certificateHighestKernel1_7Tests a).1 = 0 <;> simp [certificateRestrictedRaising, h]
  exact certificateHighestPhysical_reconstruct {0, 1, 2} certificateHighestKernel1_7Weight certificateLocalFrame1_7
    certificateHighestKernel1_7columns_highest certificateHighestKernel1_7Rows certificateHighestKernel1_7Rows_injective
    certificateHighestKernel1_7Rows_cover certificateHighestKernel1_7Tests certificateHighestKernel1_7U certificateHighestKernel1_7P certificateHighestKernel1_7R certificateHighestKernel1_7W
    certificateHighestKernel1_7U_bound hR certificateHighestKernel1_7denominator certificateHighestKernel1_7denominator_ne_zero
    certificateHighestKernel1_7reconstruction v hv

/-- The actual physical highest-vector space equals the range of this original frame. -/
theorem certificateHighestKernel1_7highest_iff_range (v : CertificateLocalWord → ℂ) :
    certificateIsHighest {0, 1, 2} certificateHighestKernel1_7Weight v ↔
      ∃ a : Fin 6 → ℂ, (certificateLocalFrame1_7.map (Int.cast : ℤ → ℂ)) *ᵥ a = v := by
  constructor
  · intro hv
    exact ⟨certificateHighestKernel1_7P.map (Int.cast : ℤ → ℂ) *ᵥ (v ∘ certificateHighestKernel1_7Rows),
      (certificateHighestKernel1_7highest_reconstruct v hv).symm⟩
  · rintro ⟨a, rfl⟩
    exact certificateHighestPhysical_mulVec {0, 1, 2} certificateHighestKernel1_7Weight _ certificateHighestKernel1_7columns_highest a

/-- Generator commutation determines source action; no action premise remains. -/
theorem certificateHighestKernel1_7source_action
    (M : Matrix CertificateLocalWord CertificateLocalWord ℂ)
    (hcomm : ∀ i j : Fin 3, M * (certificateLocalGenerator {0, 1, 2} i j).map (Int.cast : ℤ → ℂ) =
      (certificateLocalGenerator {0, 1, 2} i j).map (Int.cast : ℤ → ℂ) * M) :
    M * (certificateLocalFrame1_7.map (Int.cast : ℤ → ℂ)) = (certificateLocalFrame1_7.map (Int.cast : ℤ → ℂ)) *
      (certificateHighestKernel1_7P.map (Int.cast : ℤ → ℂ) * (M * (certificateLocalFrame1_7.map (Int.cast : ℤ → ℂ))).submatrix certificateHighestKernel1_7Rows id) :=
  certificateHighestPhysical_source_action {0, 1, 2} certificateHighestKernel1_7Weight _ certificateHighestKernel1_7Rows
    (certificateHighestKernel1_7P.map (Int.cast : ℤ → ℂ)) certificateHighestKernel1_7columns_highest
    certificateHighestKernel1_7highest_reconstruct M hcomm

/-- The action uses the archive original Gram metric and actual physical compression. -/
theorem certificateHighestKernel1_7weighted_action
    (M : Matrix CertificateLocalWord CertificateLocalWord ℂ)
    (hcomm : ∀ i j : Fin 3, M * (certificateLocalGenerator {0, 1, 2} i j).map (Int.cast : ℤ → ℂ) =
      (certificateLocalGenerator {0, 1, 2} i j).map (Int.cast : ℤ → ℂ) * M) :
    M * (certificateLocalFrame1_7.map (Int.cast : ℤ → ℂ)) = (certificateLocalFrame1_7.map (Int.cast : ℤ → ℂ)) *
      ((certificateLocalGram1_7.map (Int.cast : ℤ → ℂ))⁻¹ * ((certificateLocalFrame1_7.map (Int.cast : ℤ → ℂ))ᴴ * M * (certificateLocalFrame1_7.map (Int.cast : ℤ → ℂ)))) := by
  have hgram : (certificateLocalFrame1_7.map (Int.cast : ℤ → ℂ))ᴴ * (certificateLocalFrame1_7.map (Int.cast : ℤ → ℂ)) = certificateLocalGram1_7.map (Int.cast : ℤ → ℂ) := by
    rw [certificateIntGram_cast_complex, certificateLocalGram1_7_correct]
  have hpos : ((certificateLocalFrame1_7.map (Int.cast : ℤ → ℂ))ᴴ * (certificateLocalFrame1_7.map (Int.cast : ℤ → ℂ))).PosDef := by
    rw [hgram]
    exact certificateLocalGram1_7_posDef
  have h := certificateHighestPhysical_weighted_action (certificateLocalFrame1_7.map (Int.cast : ℤ → ℂ)) M _
    (certificateHighestKernel1_7source_action M hcomm) hpos
  rwa [hgram] at h

/-- Unconditional recovered source action for every complex physical diagram combination. -/
theorem certificateHighestKernel1_7diagram_action (weight : Equiv.Perm (Fin 6) → ℂ) :
    certificateLocalDiagramCombination {3, 4, 5} weight * (certificateLocalFrame1_7.map (Int.cast : ℤ → ℂ)) = (certificateLocalFrame1_7.map (Int.cast : ℤ → ℂ)) *
      ((certificateLocalGram1_7.map (Int.cast : ℤ → ℂ))⁻¹ *
        ((certificateLocalFrame1_7.map (Int.cast : ℤ → ℂ))ᴴ * certificateLocalDiagramCombination {3, 4, 5} weight * (certificateLocalFrame1_7.map (Int.cast : ℤ → ℂ)))) := by
  apply certificateHighestKernel1_7weighted_action
  intro i j
  apply certificateDiagramCombination_commutes_of_each
  intro σ
  have h : ({3, 4, 5} : Finset (Fin 6))ᶜ = {0, 1, 2} := by decide
  simpa only [h] using certificateLocalDiagram_generator_complex {3, 4, 5} σ i j

end ThreeCopyQutritWerner
