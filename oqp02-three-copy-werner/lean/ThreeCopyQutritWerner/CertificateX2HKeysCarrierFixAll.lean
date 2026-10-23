module

public import ThreeCopyQutritWerner.CertificateX2HKeysTranspFacts
public import ThreeCopyQutritWerner.CertificateX2HKeysTranspCheck

@[expose] public section


/-! `carrier_fix` (mirror form) for every h key: the carrier fixes every h image. -/

set_option maxRecDepth 100000

namespace ThreeCopyQutritWerner.X2Sites

open X2

theorem x2hCarrierFix_all (b : x2Key 0) : x2hCarrier (x2hTau b) * x2hImage b = x2hImage b := by
  obtain ⟨h12, h34, hT⟩ := x2hTransp_ids_of_check b (keyCheck_all b)
  exact x2hCarrierFix b h12 h34 hT

end ThreeCopyQutritWerner.X2Sites
