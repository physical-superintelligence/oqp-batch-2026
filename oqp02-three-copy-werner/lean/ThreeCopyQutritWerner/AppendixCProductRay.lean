module

public import ThreeCopyQutritWerner.ProductRayOtherSites
public import ThreeCopyQutritWerner.ProductRayUnitary

@[expose] public section


/-!
# Appendix C: product-ray equality input

The local rational comparison, exact energy completion, rank-two factorization
and unitary covariance combine to the manuscript's literal `AppCInput2`.
This argument has no global endpoint-positivity or certificate hypothesis.
-/

noncomputable section

namespace ThreeCopyQutritWerner

/-- A rank-two endpoint zero containing a fully product source ray is locally thin
at every site. The definitions are exactly those of the original Appendix C input. -/
theorem appCInput2_product_ray : AppCInput2 := by
  intro C hr hzero hprod
  obtain ⟨U₁, U₂, U₃, h₁, h₂, h₃, hrange⟩ :=
    productRay_unitaries_canonical_in_range C hprod
  have hthin := canonical_product_ray_zero_localRangeDims (embed₃ U₁ U₂ U₃ C)
    ((productRay_rank_embed₃ h₁ h₂ h₃ C).trans hr)
    ((productRay_endpointEnergy_embed₃ h₁ h₂ h₃ C).trans hzero) hrange
  simpa only [productRay_localRangeDim₁_embed₃ h₁ h₂ h₃,
    productRay_localRangeDim₂_embed₃ h₁ h₂ h₃,
    productRay_localRangeDim₃_embed₃ h₁ h₂ h₃] using hthin

end ThreeCopyQutritWerner
