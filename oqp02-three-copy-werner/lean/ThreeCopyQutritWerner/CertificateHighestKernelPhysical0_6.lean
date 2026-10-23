module

public import ThreeCopyQutritWerner.CertificateHighestKernelChecks0_6
public import ThreeCopyQutritWerner.CertificateHighestKernelPhysical

@[expose] public section


/-! Exact physical highest space and recovered operator action for one original frame.
All finite reconstruction premises are discharged by the source-bound checks. -/

noncomputable section

open scoped BigOperators Matrix ComplexOrder

namespace ThreeCopyQutritWerner

theorem certificateHighestKernel0_6columns_highest (j : Fin 11) :
    certificateIsHighest {5} certificateHighestKernel0_6Weight (fun w => (certificateLocalFrame0_6 w j : ℂ)) :=
  certificateIntFrame_columns_highest {5} certificateHighestKernel0_6Weight certificateLocalFrame0_6
    certificateLocalFrame0_6_weight certificateLocalFrame0_6_raising01 certificateLocalFrame0_6_raising12 j

/-- Every physical highest vector has the original, explicitly reconstructed coefficients. -/
theorem certificateHighestKernel0_6highest_reconstruct (v : CertificateLocalWord → ℂ)
    (hv : certificateIsHighest {5} certificateHighestKernel0_6Weight v) :
    v = (certificateLocalFrame0_6.map (Int.cast : ℤ → ℂ)) *ᵥ
      (certificateHighestKernel0_6P.map (Int.cast : ℤ → ℂ) *ᵥ (v ∘ certificateHighestKernel0_6Rows)) := by
  have hR : certificateHighestKernel0_6R = certificateRestrictedRaising {5} certificateHighestKernel0_6Rows certificateHighestKernel0_6Tests := by
    ext a c
    rw [certificateHighestKernel0_6R_bound]
    by_cases h : (certificateHighestKernel0_6Tests a).1 = 0 <;> simp [certificateRestrictedRaising, h]
  exact certificateHighestPhysical_reconstruct {5} certificateHighestKernel0_6Weight certificateLocalFrame0_6
    certificateHighestKernel0_6columns_highest certificateHighestKernel0_6Rows certificateHighestKernel0_6Rows_injective
    certificateHighestKernel0_6Rows_cover certificateHighestKernel0_6Tests certificateHighestKernel0_6U certificateHighestKernel0_6P certificateHighestKernel0_6R certificateHighestKernel0_6W
    certificateHighestKernel0_6U_bound hR certificateHighestKernel0_6denominator certificateHighestKernel0_6denominator_ne_zero
    certificateHighestKernel0_6reconstruction v hv

/-- The actual physical highest-vector space equals the range of this original frame. -/
theorem certificateHighestKernel0_6highest_iff_range (v : CertificateLocalWord → ℂ) :
    certificateIsHighest {5} certificateHighestKernel0_6Weight v ↔
      ∃ a : Fin 11 → ℂ, (certificateLocalFrame0_6.map (Int.cast : ℤ → ℂ)) *ᵥ a = v := by
  constructor
  · intro hv
    exact ⟨certificateHighestKernel0_6P.map (Int.cast : ℤ → ℂ) *ᵥ (v ∘ certificateHighestKernel0_6Rows),
      (certificateHighestKernel0_6highest_reconstruct v hv).symm⟩
  · rintro ⟨a, rfl⟩
    exact certificateHighestPhysical_mulVec {5} certificateHighestKernel0_6Weight _ certificateHighestKernel0_6columns_highest a

/-- Generator commutation determines source action; no action premise remains. -/
theorem certificateHighestKernel0_6source_action
    (M : Matrix CertificateLocalWord CertificateLocalWord ℂ)
    (hcomm : ∀ i j : Fin 3, M * (certificateLocalGenerator {5} i j).map (Int.cast : ℤ → ℂ) =
      (certificateLocalGenerator {5} i j).map (Int.cast : ℤ → ℂ) * M) :
    M * (certificateLocalFrame0_6.map (Int.cast : ℤ → ℂ)) = (certificateLocalFrame0_6.map (Int.cast : ℤ → ℂ)) *
      (certificateHighestKernel0_6P.map (Int.cast : ℤ → ℂ) * (M * (certificateLocalFrame0_6.map (Int.cast : ℤ → ℂ))).submatrix certificateHighestKernel0_6Rows id) :=
  certificateHighestPhysical_source_action {5} certificateHighestKernel0_6Weight _ certificateHighestKernel0_6Rows
    (certificateHighestKernel0_6P.map (Int.cast : ℤ → ℂ)) certificateHighestKernel0_6columns_highest
    certificateHighestKernel0_6highest_reconstruct M hcomm

/-- The action uses the archive original Gram metric and actual physical compression. -/
theorem certificateHighestKernel0_6weighted_action
    (M : Matrix CertificateLocalWord CertificateLocalWord ℂ)
    (hcomm : ∀ i j : Fin 3, M * (certificateLocalGenerator {5} i j).map (Int.cast : ℤ → ℂ) =
      (certificateLocalGenerator {5} i j).map (Int.cast : ℤ → ℂ) * M) :
    M * (certificateLocalFrame0_6.map (Int.cast : ℤ → ℂ)) = (certificateLocalFrame0_6.map (Int.cast : ℤ → ℂ)) *
      ((certificateLocalGram0_6.map (Int.cast : ℤ → ℂ))⁻¹ * ((certificateLocalFrame0_6.map (Int.cast : ℤ → ℂ))ᴴ * M * (certificateLocalFrame0_6.map (Int.cast : ℤ → ℂ)))) := by
  have hgram : (certificateLocalFrame0_6.map (Int.cast : ℤ → ℂ))ᴴ * (certificateLocalFrame0_6.map (Int.cast : ℤ → ℂ)) = certificateLocalGram0_6.map (Int.cast : ℤ → ℂ) := by
    rw [certificateIntGram_cast_complex, certificateLocalGram0_6_correct]
  have hpos : ((certificateLocalFrame0_6.map (Int.cast : ℤ → ℂ))ᴴ * (certificateLocalFrame0_6.map (Int.cast : ℤ → ℂ))).PosDef := by
    rw [hgram]
    exact certificateLocalGram0_6_posDef
  have h := certificateHighestPhysical_weighted_action (certificateLocalFrame0_6.map (Int.cast : ℤ → ℂ)) M _
    (certificateHighestKernel0_6source_action M hcomm) hpos
  rwa [hgram] at h

/-- Unconditional recovered source action for every complex physical diagram combination. -/
theorem certificateHighestKernel0_6diagram_action (weight : Equiv.Perm (Fin 6) → ℂ) :
    certificateLocalDiagramCombination {5} weight * (certificateLocalFrame0_6.map (Int.cast : ℤ → ℂ)) = (certificateLocalFrame0_6.map (Int.cast : ℤ → ℂ)) *
      ((certificateLocalGram0_6.map (Int.cast : ℤ → ℂ))⁻¹ *
        ((certificateLocalFrame0_6.map (Int.cast : ℤ → ℂ))ᴴ * certificateLocalDiagramCombination {5} weight * (certificateLocalFrame0_6.map (Int.cast : ℤ → ℂ)))) := by
  apply certificateHighestKernel0_6weighted_action
  intro i j
  apply certificateDiagramCombination_commutes_of_each
  intro σ
  exact certificateLocalDiagram_complement_generator_complex {5} σ i j

end ThreeCopyQutritWerner
