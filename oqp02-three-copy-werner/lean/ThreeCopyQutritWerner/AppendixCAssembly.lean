module

public import ThreeCopyQutritWerner.ZeroReserveRigidity
public import ThreeCopyQutritWerner.AppendixCProductRay
public import ThreeCopyQutritWerner.ThinOriginalClassification
public import ThreeCopyQutritWerner.ZeroRelationsReduction

@[expose] public section


/-! Assemble the three original analytic Appendix C inputs. The certificate
implication is kept as the literal known-feature-span hypothesis; none of the
analytic inputs is assumed. -/
noncomputable section
open scoped Matrix
namespace ThreeCopyQutritWerner

theorem appendixC_analytic_inputs : AppCInput1 ∧ AppCInput2 ∧ AppCInput3 :=
  ⟨appCInput1_proved, appCInput2_product_ray, appCInput3_proved⟩

/-- The original three zero relations suffice for an actual rank-two endpoint
zero; the rank-zero and rank-one analytic branches are now discharged. -/
theorem hasThinLocalRange_of_zeroRelations_proved
    (X : Matrix QutritSites (Fin 2) ℂ) (B : Matrix (Fin 2) QutritSites ℂ)
    (hr : (X * B).rank = 2) (hq : endpointEnergy (X * B) = 0)
    (hrel : ZeroRelations (hFeature (X * B) (bivecMat X)) (bivecMat X)) :
    HasThinLocalRange (X * B) :=
  hasThinLocalRange_of_zeroRelations appCInput1_proved appCInput2_product_ray
    X B hr hq hrel

/-- The remaining premise is exactly the original saturated-kernel span
implication for all normalized endpoint-zero factorizations. -/
theorem thinSourceProperty_of_knownZeroFeatureSpan_proved
    (hspan : ∀ (X : Matrix QutritSites (Fin 2) ℂ) (B : Matrix (Fin 2) QutritSites ℂ),
      (X * B).rank = 2 → invN (X * B) = 1 → endpointEnergy (X * B) = 0 →
        featureH (X * B) (bivecMat X) ∈ knownZeroFeatureSpan) :
    ThinSourceProperty :=
  thinSourceProperty_of_knownZeroFeatureSpan appCInput1_proved appCInput2_product_ray hspan

theorem qutritZeroClassification_of_thinSource_proved (hthin : ThinSourceProperty) :
    QutritZeroClassification :=
  qutritZeroClassification_of_thinSource hthin appCInput3_proved

/-- All three analytic Appendix C inputs are proved. The original certificate
kernel-span implication remains explicit, and is not inferred from the known
family direction. -/
theorem qutritZeroClassification_of_knownZeroFeatureSpan_proved
    (hspan : ∀ (X : Matrix QutritSites (Fin 2) ℂ) (B : Matrix (Fin 2) QutritSites ℂ),
      (X * B).rank = 2 → invN (X * B) = 1 → endpointEnergy (X * B) = 0 →
        featureH (X * B) (bivecMat X) ∈ knownZeroFeatureSpan) :
    QutritZeroClassification :=
  qutritZeroClassification_of_thinSource_proved
    (thinSourceProperty_of_knownZeroFeatureSpan_proved hspan)

/-- On a thin local source the original normalized endpoint zero has both
nonzero singular values equal to 1/sqrt(2), expressed by its actual Gram square. -/
theorem isNormalizedHalfSingularZero_of_thin_endpoint_zero
    (C : Matrix QutritSites QutritSites ℂ) (hr : C.rank ≤ 2)
    (hN : invN C = 1) (hq : endpointEnergy C = 0) (hthin : HasThinLocalRange C) :
    IsNormalizedHalfSingularZero C :=
  isNormalizedHalfSingularZero_of_isQutritZeroFamilyMember
    (appCInput3_proved C hr hN hq hthin)

/-- Exact equality with the original displayed union, conditional only on
the still-open thin-source conclusion. -/
theorem isQutritZeroFamilyMember_iff_normalized_endpoint_zero
    (hthin : ThinSourceProperty) (C : Matrix QutritSites QutritSites ℂ) :
    IsQutritZeroFamilyMember C ↔ C.rank ≤ 2 ∧ invN C = 1 ∧ endpointEnergy C = 0 := by
  constructor
  · intro hC
    have h := isNormalizedHalfSingularZero_of_isQutritZeroFamilyMember hC
    exact ⟨h.1, h.2.1, h.2.2.1⟩
  · rintro ⟨hr, hN, hq⟩
    exact qutritZeroClassification_of_thinSource_proved hthin C hr hN hq

end ThreeCopyQutritWerner
