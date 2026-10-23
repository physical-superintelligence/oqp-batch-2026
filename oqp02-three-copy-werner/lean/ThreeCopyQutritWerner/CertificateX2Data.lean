module

public import ThreeCopyQutritWerner.CertificateX2Reduced
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2Trans

@[expose] public section


/-! The concrete data of the bridge's reduced statement.

`x2DataConcrete : X2Data` takes the images from CertificateX2Images (packed copy of the certificate's 414 `J`) and the
exact parity transfers from CertificateX2Trans. CertificateX2Reduced is the module. The kernel cross-checks below compare the packed data with
the bridge's own tables: column counts with `x2GlobalSize`, ambient dimensions with `x2Mult ∘ x2GlobalTypes`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThreeCopyQutritWerner

/-- The concrete route-X2 data: images `J` and parity transfers `transS`, `transA`. -/
noncomputable def x2DataConcrete : X2Data where
  image s b := x2ImageOfFlat (Matrix.of fun
    (i : Fin (x2KeyMult s b 0 * x2KeyMult s b 1 * x2KeyMult s b 2)) (c : Fin (x2KeySize s b)) =>
      X2.x2JEntry (x2KeyGlobal s b) i c)
  transS := X2.x2TransS
  transA := X2.x2TransA

/-- Sector of a global key (h 0-121, m 122-290, a 291-413). -/
def x2GlobalSector (g : ℕ) : Fin 3 := if g < 122 then 0 else if g < 291 then 1 else 2

/-- The packed images have exactly the bridge's column counts. -/
theorem x2DataConcrete_sizes : (List.range 414).all (fun g =>
    if h : g < 414 then X2.x2JSize.getD g 0 == x2GlobalSize ⟨g, h⟩ else true) = true := by
  decide +kernel

/-- The packed images have exactly the bridge's ambient dimensions `m₀ m₁ m₂`. -/
theorem x2DataConcrete_ambients : (List.range 414).all (fun g =>
    if h : g < 414 then
      X2.x2JAmb.getD g 0 == x2Mult (x2GlobalSector g) (x2GlobalTypes ⟨g, h⟩ 0) *
        x2Mult (x2GlobalSector g) (x2GlobalTypes ⟨g, h⟩ 1) *
        x2Mult (x2GlobalSector g) (x2GlobalTypes ⟨g, h⟩ 2)
    else true) = true := by
  decide +kernel

end ThreeCopyQutritWerner
