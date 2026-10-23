module

public import ThreeCopyQutritWerner.CertificateHighestKernelChecks0_4
public import ThreeCopyQutritWerner.CertificateHighestKernelPhysical

@[expose] public section


/-! Exact physical highest space and recovered operator action for one original frame.
All finite reconstruction premises are discharged by the source-bound checks. -/

noncomputable section

open scoped BigOperators Matrix ComplexOrder

namespace ThreeCopyQutritWerner

theorem certificateHighestKernel0_4columns_highest (j : Fin 15) :
    certificateIsHighest {5} certificateHighestKernel0_4Weight (fun w => (certificateLocalFrame0_4 w j : ℂ)) :=
  certificateIntFrame_columns_highest {5} certificateHighestKernel0_4Weight certificateLocalFrame0_4
    certificateLocalFrame0_4_weight certificateLocalFrame0_4_raising01 certificateLocalFrame0_4_raising12 j

/-- Every physical highest vector has the original, explicitly reconstructed coefficients. -/
theorem certificateHighestKernel0_4highest_reconstruct (v : CertificateLocalWord → ℂ)
    (hv : certificateIsHighest {5} certificateHighestKernel0_4Weight v) :
    v = (certificateLocalFrame0_4.map (Int.cast : ℤ → ℂ)) *ᵥ
      (certificateHighestKernel0_4P.map (Int.cast : ℤ → ℂ) *ᵥ (v ∘ certificateHighestKernel0_4Rows)) := by
  have hR : certificateHighestKernel0_4R = certificateRestrictedRaising {5} certificateHighestKernel0_4Rows certificateHighestKernel0_4Tests := by
    ext a c
    rw [certificateHighestKernel0_4R_bound]
    by_cases h : (certificateHighestKernel0_4Tests a).1 = 0 <;> simp [certificateRestrictedRaising, h]
  exact certificateHighestPhysical_reconstruct {5} certificateHighestKernel0_4Weight certificateLocalFrame0_4
    certificateHighestKernel0_4columns_highest certificateHighestKernel0_4Rows certificateHighestKernel0_4Rows_injective
    certificateHighestKernel0_4Rows_cover certificateHighestKernel0_4Tests certificateHighestKernel0_4U certificateHighestKernel0_4P certificateHighestKernel0_4R certificateHighestKernel0_4W
    certificateHighestKernel0_4U_bound hR certificateHighestKernel0_4denominator certificateHighestKernel0_4denominator_ne_zero
    certificateHighestKernel0_4reconstruction v hv

/-- The actual physical highest-vector space equals the range of this original frame. -/
theorem certificateHighestKernel0_4highest_iff_range (v : CertificateLocalWord → ℂ) :
    certificateIsHighest {5} certificateHighestKernel0_4Weight v ↔
      ∃ a : Fin 15 → ℂ, (certificateLocalFrame0_4.map (Int.cast : ℤ → ℂ)) *ᵥ a = v := by
  constructor
  · intro hv
    exact ⟨certificateHighestKernel0_4P.map (Int.cast : ℤ → ℂ) *ᵥ (v ∘ certificateHighestKernel0_4Rows),
      (certificateHighestKernel0_4highest_reconstruct v hv).symm⟩
  · rintro ⟨a, rfl⟩
    exact certificateHighestPhysical_mulVec {5} certificateHighestKernel0_4Weight _ certificateHighestKernel0_4columns_highest a

/-- Generator commutation determines source action; no action premise remains. -/
theorem certificateHighestKernel0_4source_action
    (M : Matrix CertificateLocalWord CertificateLocalWord ℂ)
    (hcomm : ∀ i j : Fin 3, M * (certificateLocalGenerator {5} i j).map (Int.cast : ℤ → ℂ) =
      (certificateLocalGenerator {5} i j).map (Int.cast : ℤ → ℂ) * M) :
    M * (certificateLocalFrame0_4.map (Int.cast : ℤ → ℂ)) = (certificateLocalFrame0_4.map (Int.cast : ℤ → ℂ)) *
      (certificateHighestKernel0_4P.map (Int.cast : ℤ → ℂ) * (M * (certificateLocalFrame0_4.map (Int.cast : ℤ → ℂ))).submatrix certificateHighestKernel0_4Rows id) :=
  certificateHighestPhysical_source_action {5} certificateHighestKernel0_4Weight _ certificateHighestKernel0_4Rows
    (certificateHighestKernel0_4P.map (Int.cast : ℤ → ℂ)) certificateHighestKernel0_4columns_highest
    certificateHighestKernel0_4highest_reconstruct M hcomm

/-- The action uses the archive original Gram metric and actual physical compression. -/
theorem certificateHighestKernel0_4weighted_action
    (M : Matrix CertificateLocalWord CertificateLocalWord ℂ)
    (hcomm : ∀ i j : Fin 3, M * (certificateLocalGenerator {5} i j).map (Int.cast : ℤ → ℂ) =
      (certificateLocalGenerator {5} i j).map (Int.cast : ℤ → ℂ) * M) :
    M * (certificateLocalFrame0_4.map (Int.cast : ℤ → ℂ)) = (certificateLocalFrame0_4.map (Int.cast : ℤ → ℂ)) *
      ((certificateLocalGram0_4.map (Int.cast : ℤ → ℂ))⁻¹ * ((certificateLocalFrame0_4.map (Int.cast : ℤ → ℂ))ᴴ * M * (certificateLocalFrame0_4.map (Int.cast : ℤ → ℂ)))) := by
  have hgram : (certificateLocalFrame0_4.map (Int.cast : ℤ → ℂ))ᴴ * (certificateLocalFrame0_4.map (Int.cast : ℤ → ℂ)) = certificateLocalGram0_4.map (Int.cast : ℤ → ℂ) := by
    rw [certificateIntGram_cast_complex, certificateLocalGram0_4_correct]
  have hpos : ((certificateLocalFrame0_4.map (Int.cast : ℤ → ℂ))ᴴ * (certificateLocalFrame0_4.map (Int.cast : ℤ → ℂ))).PosDef := by
    rw [hgram]
    exact certificateLocalGram0_4_posDef
  have h := certificateHighestPhysical_weighted_action (certificateLocalFrame0_4.map (Int.cast : ℤ → ℂ)) M _
    (certificateHighestKernel0_4source_action M hcomm) hpos
  rwa [hgram] at h

/-- Unconditional recovered source action for every complex physical diagram combination. -/
theorem certificateHighestKernel0_4diagram_action (weight : Equiv.Perm (Fin 6) → ℂ) :
    certificateLocalDiagramCombination {5} weight * (certificateLocalFrame0_4.map (Int.cast : ℤ → ℂ)) = (certificateLocalFrame0_4.map (Int.cast : ℤ → ℂ)) *
      ((certificateLocalGram0_4.map (Int.cast : ℤ → ℂ))⁻¹ *
        ((certificateLocalFrame0_4.map (Int.cast : ℤ → ℂ))ᴴ * certificateLocalDiagramCombination {5} weight * (certificateLocalFrame0_4.map (Int.cast : ℤ → ℂ)))) := by
  apply certificateHighestKernel0_4weighted_action
  intro i j
  apply certificateDiagramCombination_commutes_of_each
  intro σ
  exact certificateLocalDiagram_complement_generator_complex {5} σ i j

end ThreeCopyQutritWerner
