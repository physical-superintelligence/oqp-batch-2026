module

public import ThreeCopyQutritWerner.CertificateHighestKernelChecks2_0
public import ThreeCopyQutritWerner.CertificateHighestKernelPhysical

@[expose] public section


/-! Exact physical highest space and recovered operator action for one original frame.
All finite reconstruction premises are discharged by the source-bound checks. -/

noncomputable section

open scoped BigOperators Matrix ComplexOrder

namespace ThreeCopyQutritWerner

theorem certificateHighestKernel2_0columns_highest (j : Fin 1) :
    certificateIsHighest {0} certificateHighestKernel2_0Weight (fun w => (certificateLocalFrame2_0 w j : ℂ)) :=
  certificateIntFrame_columns_highest {0} certificateHighestKernel2_0Weight certificateLocalFrame2_0
    certificateLocalFrame2_0_weight certificateLocalFrame2_0_raising01 certificateLocalFrame2_0_raising12 j

/-- Every physical highest vector has the original, explicitly reconstructed coefficients. -/
theorem certificateHighestKernel2_0highest_reconstruct (v : CertificateLocalWord → ℂ)
    (hv : certificateIsHighest {0} certificateHighestKernel2_0Weight v) :
    v = (certificateLocalFrame2_0.map (Int.cast : ℤ → ℂ)) *ᵥ
      (certificateHighestKernel2_0P.map (Int.cast : ℤ → ℂ) *ᵥ (v ∘ certificateHighestKernel2_0Rows)) := by
  have hR : certificateHighestKernel2_0R = certificateRestrictedRaising {0} certificateHighestKernel2_0Rows certificateHighestKernel2_0Tests := by
    ext a c
    rw [certificateHighestKernel2_0R_bound]
    by_cases h : (certificateHighestKernel2_0Tests a).1 = 0 <;> simp [certificateRestrictedRaising, h]
  exact certificateHighestPhysical_reconstruct {0} certificateHighestKernel2_0Weight certificateLocalFrame2_0
    certificateHighestKernel2_0columns_highest certificateHighestKernel2_0Rows certificateHighestKernel2_0Rows_injective
    certificateHighestKernel2_0Rows_cover certificateHighestKernel2_0Tests certificateHighestKernel2_0U certificateHighestKernel2_0P certificateHighestKernel2_0R certificateHighestKernel2_0W
    certificateHighestKernel2_0U_bound hR certificateHighestKernel2_0denominator certificateHighestKernel2_0denominator_ne_zero
    certificateHighestKernel2_0reconstruction v hv

/-- The actual physical highest-vector space equals the range of this original frame. -/
theorem certificateHighestKernel2_0highest_iff_range (v : CertificateLocalWord → ℂ) :
    certificateIsHighest {0} certificateHighestKernel2_0Weight v ↔
      ∃ a : Fin 1 → ℂ, (certificateLocalFrame2_0.map (Int.cast : ℤ → ℂ)) *ᵥ a = v := by
  constructor
  · intro hv
    exact ⟨certificateHighestKernel2_0P.map (Int.cast : ℤ → ℂ) *ᵥ (v ∘ certificateHighestKernel2_0Rows),
      (certificateHighestKernel2_0highest_reconstruct v hv).symm⟩
  · rintro ⟨a, rfl⟩
    exact certificateHighestPhysical_mulVec {0} certificateHighestKernel2_0Weight _ certificateHighestKernel2_0columns_highest a

/-- Generator commutation determines source action; no action premise remains. -/
theorem certificateHighestKernel2_0source_action
    (M : Matrix CertificateLocalWord CertificateLocalWord ℂ)
    (hcomm : ∀ i j : Fin 3, M * (certificateLocalGenerator {0} i j).map (Int.cast : ℤ → ℂ) =
      (certificateLocalGenerator {0} i j).map (Int.cast : ℤ → ℂ) * M) :
    M * (certificateLocalFrame2_0.map (Int.cast : ℤ → ℂ)) = (certificateLocalFrame2_0.map (Int.cast : ℤ → ℂ)) *
      (certificateHighestKernel2_0P.map (Int.cast : ℤ → ℂ) * (M * (certificateLocalFrame2_0.map (Int.cast : ℤ → ℂ))).submatrix certificateHighestKernel2_0Rows id) :=
  certificateHighestPhysical_source_action {0} certificateHighestKernel2_0Weight _ certificateHighestKernel2_0Rows
    (certificateHighestKernel2_0P.map (Int.cast : ℤ → ℂ)) certificateHighestKernel2_0columns_highest
    certificateHighestKernel2_0highest_reconstruct M hcomm

/-- The action uses the archive original Gram metric and actual physical compression. -/
theorem certificateHighestKernel2_0weighted_action
    (M : Matrix CertificateLocalWord CertificateLocalWord ℂ)
    (hcomm : ∀ i j : Fin 3, M * (certificateLocalGenerator {0} i j).map (Int.cast : ℤ → ℂ) =
      (certificateLocalGenerator {0} i j).map (Int.cast : ℤ → ℂ) * M) :
    M * (certificateLocalFrame2_0.map (Int.cast : ℤ → ℂ)) = (certificateLocalFrame2_0.map (Int.cast : ℤ → ℂ)) *
      ((certificateLocalGram2_0.map (Int.cast : ℤ → ℂ))⁻¹ * ((certificateLocalFrame2_0.map (Int.cast : ℤ → ℂ))ᴴ * M * (certificateLocalFrame2_0.map (Int.cast : ℤ → ℂ)))) := by
  have hgram : (certificateLocalFrame2_0.map (Int.cast : ℤ → ℂ))ᴴ * (certificateLocalFrame2_0.map (Int.cast : ℤ → ℂ)) = certificateLocalGram2_0.map (Int.cast : ℤ → ℂ) := by
    rw [certificateIntGram_cast_complex, certificateLocalGram2_0_correct]
  have hpos : ((certificateLocalFrame2_0.map (Int.cast : ℤ → ℂ))ᴴ * (certificateLocalFrame2_0.map (Int.cast : ℤ → ℂ))).PosDef := by
    rw [hgram]
    exact certificateLocalGram2_0_posDef
  have h := certificateHighestPhysical_weighted_action (certificateLocalFrame2_0.map (Int.cast : ℤ → ℂ)) M _
    (certificateHighestKernel2_0source_action M hcomm) hpos
  rwa [hgram] at h

/-- Unconditional recovered source action for every complex physical diagram combination. -/
theorem certificateHighestKernel2_0diagram_action (weight : Equiv.Perm (Fin 6) → ℂ) :
    certificateLocalDiagramCombination {1, 2, 3, 4, 5} weight * (certificateLocalFrame2_0.map (Int.cast : ℤ → ℂ)) = (certificateLocalFrame2_0.map (Int.cast : ℤ → ℂ)) *
      ((certificateLocalGram2_0.map (Int.cast : ℤ → ℂ))⁻¹ *
        ((certificateLocalFrame2_0.map (Int.cast : ℤ → ℂ))ᴴ * certificateLocalDiagramCombination {1, 2, 3, 4, 5} weight * (certificateLocalFrame2_0.map (Int.cast : ℤ → ℂ)))) := by
  apply certificateHighestKernel2_0weighted_action
  intro i j
  apply certificateDiagramCombination_commutes_of_each
  intro σ
  have h : ({1, 2, 3, 4, 5} : Finset (Fin 6))ᶜ = {0} := by decide
  simpa only [h] using certificateLocalDiagram_generator_complex {1, 2, 3, 4, 5} σ i j

end ThreeCopyQutritWerner
