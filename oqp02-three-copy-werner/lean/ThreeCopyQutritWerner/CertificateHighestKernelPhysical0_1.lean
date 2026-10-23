module

public import ThreeCopyQutritWerner.CertificateHighestKernelChecks0_1
public import ThreeCopyQutritWerner.CertificateHighestKernelPhysical

@[expose] public section


/-! Exact physical highest space and recovered operator action for one original frame.
All finite reconstruction premises are discharged by the source-bound checks. -/

noncomputable section

open scoped BigOperators Matrix ComplexOrder

namespace ThreeCopyQutritWerner

theorem certificateHighestKernel0_1columns_highest (j : Fin 4) :
    certificateIsHighest {5} certificateHighestKernel0_1Weight (fun w => (certificateLocalFrame0_1 w j : ℂ)) :=
  certificateIntFrame_columns_highest {5} certificateHighestKernel0_1Weight certificateLocalFrame0_1
    certificateLocalFrame0_1_weight certificateLocalFrame0_1_raising01 certificateLocalFrame0_1_raising12 j

/-- Every physical highest vector has the original, explicitly reconstructed coefficients. -/
theorem certificateHighestKernel0_1highest_reconstruct (v : CertificateLocalWord → ℂ)
    (hv : certificateIsHighest {5} certificateHighestKernel0_1Weight v) :
    v = (certificateLocalFrame0_1.map (Int.cast : ℤ → ℂ)) *ᵥ
      (certificateHighestKernel0_1P.map (Int.cast : ℤ → ℂ) *ᵥ (v ∘ certificateHighestKernel0_1Rows)) := by
  have hR : certificateHighestKernel0_1R = certificateRestrictedRaising {5} certificateHighestKernel0_1Rows certificateHighestKernel0_1Tests := by
    ext a c
    rw [certificateHighestKernel0_1R_bound]
    by_cases h : (certificateHighestKernel0_1Tests a).1 = 0 <;> simp [certificateRestrictedRaising, h]
  exact certificateHighestPhysical_reconstruct {5} certificateHighestKernel0_1Weight certificateLocalFrame0_1
    certificateHighestKernel0_1columns_highest certificateHighestKernel0_1Rows certificateHighestKernel0_1Rows_injective
    certificateHighestKernel0_1Rows_cover certificateHighestKernel0_1Tests certificateHighestKernel0_1U certificateHighestKernel0_1P certificateHighestKernel0_1R certificateHighestKernel0_1W
    certificateHighestKernel0_1U_bound hR certificateHighestKernel0_1denominator certificateHighestKernel0_1denominator_ne_zero
    certificateHighestKernel0_1reconstruction v hv

/-- The actual physical highest-vector space equals the range of this original frame. -/
theorem certificateHighestKernel0_1highest_iff_range (v : CertificateLocalWord → ℂ) :
    certificateIsHighest {5} certificateHighestKernel0_1Weight v ↔
      ∃ a : Fin 4 → ℂ, (certificateLocalFrame0_1.map (Int.cast : ℤ → ℂ)) *ᵥ a = v := by
  constructor
  · intro hv
    exact ⟨certificateHighestKernel0_1P.map (Int.cast : ℤ → ℂ) *ᵥ (v ∘ certificateHighestKernel0_1Rows),
      (certificateHighestKernel0_1highest_reconstruct v hv).symm⟩
  · rintro ⟨a, rfl⟩
    exact certificateHighestPhysical_mulVec {5} certificateHighestKernel0_1Weight _ certificateHighestKernel0_1columns_highest a

/-- Generator commutation determines source action; no action premise remains. -/
theorem certificateHighestKernel0_1source_action
    (M : Matrix CertificateLocalWord CertificateLocalWord ℂ)
    (hcomm : ∀ i j : Fin 3, M * (certificateLocalGenerator {5} i j).map (Int.cast : ℤ → ℂ) =
      (certificateLocalGenerator {5} i j).map (Int.cast : ℤ → ℂ) * M) :
    M * (certificateLocalFrame0_1.map (Int.cast : ℤ → ℂ)) = (certificateLocalFrame0_1.map (Int.cast : ℤ → ℂ)) *
      (certificateHighestKernel0_1P.map (Int.cast : ℤ → ℂ) * (M * (certificateLocalFrame0_1.map (Int.cast : ℤ → ℂ))).submatrix certificateHighestKernel0_1Rows id) :=
  certificateHighestPhysical_source_action {5} certificateHighestKernel0_1Weight _ certificateHighestKernel0_1Rows
    (certificateHighestKernel0_1P.map (Int.cast : ℤ → ℂ)) certificateHighestKernel0_1columns_highest
    certificateHighestKernel0_1highest_reconstruct M hcomm

/-- The action uses the archive original Gram metric and actual physical compression. -/
theorem certificateHighestKernel0_1weighted_action
    (M : Matrix CertificateLocalWord CertificateLocalWord ℂ)
    (hcomm : ∀ i j : Fin 3, M * (certificateLocalGenerator {5} i j).map (Int.cast : ℤ → ℂ) =
      (certificateLocalGenerator {5} i j).map (Int.cast : ℤ → ℂ) * M) :
    M * (certificateLocalFrame0_1.map (Int.cast : ℤ → ℂ)) = (certificateLocalFrame0_1.map (Int.cast : ℤ → ℂ)) *
      ((certificateLocalGram0_1.map (Int.cast : ℤ → ℂ))⁻¹ * ((certificateLocalFrame0_1.map (Int.cast : ℤ → ℂ))ᴴ * M * (certificateLocalFrame0_1.map (Int.cast : ℤ → ℂ)))) := by
  have hgram : (certificateLocalFrame0_1.map (Int.cast : ℤ → ℂ))ᴴ * (certificateLocalFrame0_1.map (Int.cast : ℤ → ℂ)) = certificateLocalGram0_1.map (Int.cast : ℤ → ℂ) := by
    rw [certificateIntGram_cast_complex, certificateLocalGram0_1_correct]
  have hpos : ((certificateLocalFrame0_1.map (Int.cast : ℤ → ℂ))ᴴ * (certificateLocalFrame0_1.map (Int.cast : ℤ → ℂ))).PosDef := by
    rw [hgram]
    exact certificateLocalGram0_1_posDef
  have h := certificateHighestPhysical_weighted_action (certificateLocalFrame0_1.map (Int.cast : ℤ → ℂ)) M _
    (certificateHighestKernel0_1source_action M hcomm) hpos
  rwa [hgram] at h

/-- Unconditional recovered source action for every complex physical diagram combination. -/
theorem certificateHighestKernel0_1diagram_action (weight : Equiv.Perm (Fin 6) → ℂ) :
    certificateLocalDiagramCombination {5} weight * (certificateLocalFrame0_1.map (Int.cast : ℤ → ℂ)) = (certificateLocalFrame0_1.map (Int.cast : ℤ → ℂ)) *
      ((certificateLocalGram0_1.map (Int.cast : ℤ → ℂ))⁻¹ *
        ((certificateLocalFrame0_1.map (Int.cast : ℤ → ℂ))ᴴ * certificateLocalDiagramCombination {5} weight * (certificateLocalFrame0_1.map (Int.cast : ℤ → ℂ)))) := by
  apply certificateHighestKernel0_1weighted_action
  intro i j
  apply certificateDiagramCombination_commutes_of_each
  intro σ
  exact certificateLocalDiagram_complement_generator_complex {5} σ i j

end ThreeCopyQutritWerner
