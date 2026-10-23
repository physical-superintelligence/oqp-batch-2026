module

public import ThreeCopyQutritWerner.CertificateHighestKernelChecks0_0
public import ThreeCopyQutritWerner.CertificateHighestKernelPhysical

@[expose] public section


/-! Exact physical highest space and recovered operator action for one original frame.
All finite reconstruction premises are discharged by the source-bound checks. -/

noncomputable section

open scoped BigOperators Matrix ComplexOrder

namespace ThreeCopyQutritWerner

theorem certificateHighestKernel0_0columns_highest (j : Fin 1) :
    certificateIsHighest {5} certificateHighestKernel0_0Weight (fun w => (certificateLocalFrame0_0 w j : ℂ)) :=
  certificateIntFrame_columns_highest {5} certificateHighestKernel0_0Weight certificateLocalFrame0_0
    certificateLocalFrame0_0_weight certificateLocalFrame0_0_raising01 certificateLocalFrame0_0_raising12 j

/-- Every physical highest vector has the original, explicitly reconstructed coefficients. -/
theorem certificateHighestKernel0_0highest_reconstruct (v : CertificateLocalWord → ℂ)
    (hv : certificateIsHighest {5} certificateHighestKernel0_0Weight v) :
    v = (certificateLocalFrame0_0.map (Int.cast : ℤ → ℂ)) *ᵥ
      (certificateHighestKernel0_0P.map (Int.cast : ℤ → ℂ) *ᵥ (v ∘ certificateHighestKernel0_0Rows)) := by
  have hR : certificateHighestKernel0_0R = certificateRestrictedRaising {5} certificateHighestKernel0_0Rows certificateHighestKernel0_0Tests := by
    ext a c
    rw [certificateHighestKernel0_0R_bound]
    by_cases h : (certificateHighestKernel0_0Tests a).1 = 0 <;> simp [certificateRestrictedRaising, h]
  exact certificateHighestPhysical_reconstruct {5} certificateHighestKernel0_0Weight certificateLocalFrame0_0
    certificateHighestKernel0_0columns_highest certificateHighestKernel0_0Rows certificateHighestKernel0_0Rows_injective
    certificateHighestKernel0_0Rows_cover certificateHighestKernel0_0Tests certificateHighestKernel0_0U certificateHighestKernel0_0P certificateHighestKernel0_0R certificateHighestKernel0_0W
    certificateHighestKernel0_0U_bound hR certificateHighestKernel0_0denominator certificateHighestKernel0_0denominator_ne_zero
    certificateHighestKernel0_0reconstruction v hv

/-- The actual physical highest-vector space equals the range of this original frame. -/
theorem certificateHighestKernel0_0highest_iff_range (v : CertificateLocalWord → ℂ) :
    certificateIsHighest {5} certificateHighestKernel0_0Weight v ↔
      ∃ a : Fin 1 → ℂ, (certificateLocalFrame0_0.map (Int.cast : ℤ → ℂ)) *ᵥ a = v := by
  constructor
  · intro hv
    exact ⟨certificateHighestKernel0_0P.map (Int.cast : ℤ → ℂ) *ᵥ (v ∘ certificateHighestKernel0_0Rows),
      (certificateHighestKernel0_0highest_reconstruct v hv).symm⟩
  · rintro ⟨a, rfl⟩
    exact certificateHighestPhysical_mulVec {5} certificateHighestKernel0_0Weight _ certificateHighestKernel0_0columns_highest a

/-- Generator commutation determines source action; no action premise remains. -/
theorem certificateHighestKernel0_0source_action
    (M : Matrix CertificateLocalWord CertificateLocalWord ℂ)
    (hcomm : ∀ i j : Fin 3, M * (certificateLocalGenerator {5} i j).map (Int.cast : ℤ → ℂ) =
      (certificateLocalGenerator {5} i j).map (Int.cast : ℤ → ℂ) * M) :
    M * (certificateLocalFrame0_0.map (Int.cast : ℤ → ℂ)) = (certificateLocalFrame0_0.map (Int.cast : ℤ → ℂ)) *
      (certificateHighestKernel0_0P.map (Int.cast : ℤ → ℂ) * (M * (certificateLocalFrame0_0.map (Int.cast : ℤ → ℂ))).submatrix certificateHighestKernel0_0Rows id) :=
  certificateHighestPhysical_source_action {5} certificateHighestKernel0_0Weight _ certificateHighestKernel0_0Rows
    (certificateHighestKernel0_0P.map (Int.cast : ℤ → ℂ)) certificateHighestKernel0_0columns_highest
    certificateHighestKernel0_0highest_reconstruct M hcomm

/-- The action uses the archive original Gram metric and actual physical compression. -/
theorem certificateHighestKernel0_0weighted_action
    (M : Matrix CertificateLocalWord CertificateLocalWord ℂ)
    (hcomm : ∀ i j : Fin 3, M * (certificateLocalGenerator {5} i j).map (Int.cast : ℤ → ℂ) =
      (certificateLocalGenerator {5} i j).map (Int.cast : ℤ → ℂ) * M) :
    M * (certificateLocalFrame0_0.map (Int.cast : ℤ → ℂ)) = (certificateLocalFrame0_0.map (Int.cast : ℤ → ℂ)) *
      ((certificateLocalGram0_0.map (Int.cast : ℤ → ℂ))⁻¹ * ((certificateLocalFrame0_0.map (Int.cast : ℤ → ℂ))ᴴ * M * (certificateLocalFrame0_0.map (Int.cast : ℤ → ℂ)))) := by
  have hgram : (certificateLocalFrame0_0.map (Int.cast : ℤ → ℂ))ᴴ * (certificateLocalFrame0_0.map (Int.cast : ℤ → ℂ)) = certificateLocalGram0_0.map (Int.cast : ℤ → ℂ) := by
    rw [certificateIntGram_cast_complex, certificateLocalGram0_0_correct]
  have hpos : ((certificateLocalFrame0_0.map (Int.cast : ℤ → ℂ))ᴴ * (certificateLocalFrame0_0.map (Int.cast : ℤ → ℂ))).PosDef := by
    rw [hgram]
    exact certificateLocalGram0_0_posDef
  have h := certificateHighestPhysical_weighted_action (certificateLocalFrame0_0.map (Int.cast : ℤ → ℂ)) M _
    (certificateHighestKernel0_0source_action M hcomm) hpos
  rwa [hgram] at h

/-- Unconditional recovered source action for every complex physical diagram combination. -/
theorem certificateHighestKernel0_0diagram_action (weight : Equiv.Perm (Fin 6) → ℂ) :
    certificateLocalDiagramCombination {5} weight * (certificateLocalFrame0_0.map (Int.cast : ℤ → ℂ)) = (certificateLocalFrame0_0.map (Int.cast : ℤ → ℂ)) *
      ((certificateLocalGram0_0.map (Int.cast : ℤ → ℂ))⁻¹ *
        ((certificateLocalFrame0_0.map (Int.cast : ℤ → ℂ))ᴴ * certificateLocalDiagramCombination {5} weight * (certificateLocalFrame0_0.map (Int.cast : ℤ → ℂ)))) := by
  apply certificateHighestKernel0_0weighted_action
  intro i j
  apply certificateDiagramCombination_commutes_of_each
  intro σ
  exact certificateLocalDiagram_complement_generator_complex {5} σ i j

end ThreeCopyQutritWerner
