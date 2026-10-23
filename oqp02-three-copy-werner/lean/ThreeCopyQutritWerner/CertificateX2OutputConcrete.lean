module

public import ThreeCopyQutritWerner.CertificateX2Data
public import ThreeCopyQutritWerner.CertificateX2OutputTarget

@[expose] public section


/-!
# Output stage: the concrete images

For the `x2DataConcrete` (CertificateX2Data), the image of h block `b` is read from the packed
columns `X2.x2JAll.getD (x2KeyGlobal 0 b) []` of CertificateX2Images (by unfolding), with the bridge's column counts.
-/

namespace ThreeCopyQutritWerner
namespace X2

theorem x2ImageCols_concrete (b : x2Key 0) :
    X2ImageCols x2DataConcrete b (x2JAll.getD (x2KeyGlobal 0 b) []) := fun _ _ => rfl

theorem x2JAll_length_h : ∀ b : x2Key 0, (x2JAll.getD (x2KeyGlobal 0 b) []).length = x2KeySize 0 b := by
  decide +kernel

end X2
end ThreeCopyQutritWerner
