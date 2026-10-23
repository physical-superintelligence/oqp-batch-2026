module

public import ThreeCopyQutritWerner.CertificateX2OutputTgtS0
public import ThreeCopyQutritWerner.CertificateX2OutputTgtS1
public import ThreeCopyQutritWerner.CertificateX2OutputTgtS2
public import ThreeCopyQutritWerner.CertificateX2OutputTgtS3
public import ThreeCopyQutritWerner.CertificateX2OutputTgtB244k0
public import ThreeCopyQutritWerner.CertificateX2OutputTgtB244k1
public import ThreeCopyQutritWerner.CertificateX2OutputTgtB344k0
public import ThreeCopyQutritWerner.CertificateX2OutputTgtB344k1
public import ThreeCopyQutritWerner.CertificateX2OutputTgtB444k0
public import ThreeCopyQutritWerner.CertificateX2OutputTgtB444k1
public import ThreeCopyQutritWerner.CertificateX2OutputTgtB444k2
public import ThreeCopyQutritWerner.CertificateX2OutputTgtB445k0
public import ThreeCopyQutritWerner.CertificateX2OutputTgtB445k1
public import ThreeCopyQutritWerner.CertificateX2OutputTgtB446k0
public import ThreeCopyQutritWerner.CertificateX2OutputTgtB446k1
public import ThreeCopyQutritWerner.CertificateX2OutputTgtB455k0
public import ThreeCopyQutritWerner.CertificateX2OutputTgtB455k1
public import ThreeCopyQutritWerner.CertificateX2OutputTgtB456k0
public import ThreeCopyQutritWerner.CertificateX2OutputTgtB466k0
public import ThreeCopyQutritWerner.CertificateX2OutputTgtB466k1
public import ThreeCopyQutritWerner.CertificateX2OutputTgtB555k0
public import ThreeCopyQutritWerner.CertificateX2OutputTgtB555k1
public import ThreeCopyQutritWerner.CertificateX2OutputTgtB555k2
public import ThreeCopyQutritWerner.CertificateX2OutputTgtB556k0
public import ThreeCopyQutritWerner.CertificateX2OutputTgtB556k1
public import ThreeCopyQutritWerner.CertificateX2OutputTgtB566k0
public import ThreeCopyQutritWerner.CertificateX2OutputTgtB566k1
public import ThreeCopyQutritWerner.CertificateX2OutputTgtB666k0
public import ThreeCopyQutritWerner.CertificateX2OutputTgtB666k1
public import ThreeCopyQutritWerner.CertificateX2OutputTgtB666k2

@[expose] public section


/-! Output stage: the targets of all 122 h blocks as a family over `x2Key 0`:
`x2Target x2DataConcrete b = x2TgtLit b / 8`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThreeCopyQutritWerner.X2

/-- Target numerators `T8 = Jᵀ (M ⊗ M ⊗ M) J` of the 122 h blocks (over `8`). -/
def x2TgtLit : ∀ b : x2Key 0, Matrix (x2Col 0 b) (x2Col 0 b) ℤ
  | ⟨0, _⟩ => Matrix.of fun c c' => (Tgt.t8_003k0.getD c []).getD c' 0
  | ⟨1, _⟩ => Matrix.of fun c c' => (Tgt.t8_004k0.getD c []).getD c' 0
  | ⟨2, _⟩ => Matrix.of fun c c' => (Tgt.t8_005k0.getD c []).getD c' 0
  | ⟨3, _⟩ => Matrix.of fun c c' => (Tgt.t8_011k0.getD c []).getD c' 0
  | ⟨4, _⟩ => Matrix.of fun c c' => (Tgt.t8_012k0.getD c []).getD c' 0
  | ⟨5, _⟩ => Matrix.of fun c c' => (Tgt.t8_013k0.getD c []).getD c' 0
  | ⟨6, _⟩ => Matrix.of fun c c' => (Tgt.t8_014k0.getD c []).getD c' 0
  | ⟨7, _⟩ => Matrix.of fun c c' => (Tgt.t8_015k0.getD c []).getD c' 0
  | ⟨8, _⟩ => Matrix.of fun c c' => (Tgt.t8_016k0.getD c []).getD c' 0
  | ⟨9, _⟩ => Matrix.of fun c c' => (Tgt.t8_022k0.getD c []).getD c' 0
  | ⟨10, _⟩ => Matrix.of fun c c' => (Tgt.t8_023k0.getD c []).getD c' 0
  | ⟨11, _⟩ => Matrix.of fun c c' => (Tgt.t8_024k0.getD c []).getD c' 0
  | ⟨12, _⟩ => Matrix.of fun c c' => (Tgt.t8_025k0.getD c []).getD c' 0
  | ⟨13, _⟩ => Matrix.of fun c c' => (Tgt.t8_026k0.getD c []).getD c' 0
  | ⟨14, _⟩ => Matrix.of fun c c' => (Tgt.t8_033k0.getD c []).getD c' 0
  | ⟨15, _⟩ => Matrix.of fun c c' => (Tgt.t8_034k0.getD c []).getD c' 0
  | ⟨16, _⟩ => Matrix.of fun c c' => (Tgt.t8_035k0.getD c []).getD c' 0
  | ⟨17, _⟩ => Matrix.of fun c c' => (Tgt.t8_036k0.getD c []).getD c' 0
  | ⟨18, _⟩ => Matrix.of fun c c' => (Tgt.t8_044k0.getD c []).getD c' 0
  | ⟨19, _⟩ => Matrix.of fun c c' => (Tgt.t8_044k1.getD c []).getD c' 0
  | ⟨20, _⟩ => Matrix.of fun c c' => (Tgt.t8_045k0.getD c []).getD c' 0
  | ⟨21, _⟩ => Matrix.of fun c c' => (Tgt.t8_046k0.getD c []).getD c' 0
  | ⟨22, _⟩ => Matrix.of fun c c' => (Tgt.t8_055k0.getD c []).getD c' 0
  | ⟨23, _⟩ => Matrix.of fun c c' => (Tgt.t8_055k1.getD c []).getD c' 0
  | ⟨24, _⟩ => Matrix.of fun c c' => (Tgt.t8_056k0.getD c []).getD c' 0
  | ⟨25, _⟩ => Matrix.of fun c c' => (Tgt.t8_066k0.getD c []).getD c' 0
  | ⟨26, _⟩ => Matrix.of fun c c' => (Tgt.t8_066k1.getD c []).getD c' 0
  | ⟨27, _⟩ => Matrix.of fun c c' => (Tgt.t8_111k0.getD c []).getD c' 0
  | ⟨28, _⟩ => Matrix.of fun c c' => (Tgt.t8_111k2.getD c []).getD c' 0
  | ⟨29, _⟩ => Matrix.of fun c c' => (Tgt.t8_112k0.getD c []).getD c' 0
  | ⟨30, _⟩ => Matrix.of fun c c' => (Tgt.t8_112k1.getD c []).getD c' 0
  | ⟨31, _⟩ => Matrix.of fun c c' => (Tgt.t8_113k0.getD c []).getD c' 0
  | ⟨32, _⟩ => Matrix.of fun c c' => (Tgt.t8_113k1.getD c []).getD c' 0
  | ⟨33, _⟩ => Matrix.of fun c c' => (Tgt.t8_114k0.getD c []).getD c' 0
  | ⟨34, _⟩ => Matrix.of fun c c' => (Tgt.t8_114k1.getD c []).getD c' 0
  | ⟨35, _⟩ => Matrix.of fun c c' => (Tgt.t8_115k0.getD c []).getD c' 0
  | ⟨36, _⟩ => Matrix.of fun c c' => (Tgt.t8_115k1.getD c []).getD c' 0
  | ⟨37, _⟩ => Matrix.of fun c c' => (Tgt.t8_116k0.getD c []).getD c' 0
  | ⟨38, _⟩ => Matrix.of fun c c' => (Tgt.t8_116k1.getD c []).getD c' 0
  | ⟨39, _⟩ => Matrix.of fun c c' => (Tgt.t8_122k0.getD c []).getD c' 0
  | ⟨40, _⟩ => Matrix.of fun c c' => (Tgt.t8_122k1.getD c []).getD c' 0
  | ⟨41, _⟩ => Matrix.of fun c c' => (Tgt.t8_123k0.getD c []).getD c' 0
  | ⟨42, _⟩ => Matrix.of fun c c' => (Tgt.t8_124k0.getD c []).getD c' 0
  | ⟨43, _⟩ => Matrix.of fun c c' => (Tgt.t8_125k0.getD c []).getD c' 0
  | ⟨44, _⟩ => Matrix.of fun c c' => (Tgt.t8_126k0.getD c []).getD c' 0
  | ⟨45, _⟩ => Matrix.of fun c c' => (Tgt.t8_133k0.getD c []).getD c' 0
  | ⟨46, _⟩ => Matrix.of fun c c' => (Tgt.t8_133k1.getD c []).getD c' 0
  | ⟨47, _⟩ => Matrix.of fun c c' => (Tgt.t8_134k0.getD c []).getD c' 0
  | ⟨48, _⟩ => Matrix.of fun c c' => (Tgt.t8_135k0.getD c []).getD c' 0
  | ⟨49, _⟩ => Matrix.of fun c c' => (Tgt.t8_136k0.getD c []).getD c' 0
  | ⟨50, _⟩ => Matrix.of fun c c' => (Tgt.t8_144k0.getD c []).getD c' 0
  | ⟨51, _⟩ => Matrix.of fun c c' => (Tgt.t8_144k1.getD c []).getD c' 0
  | ⟨52, _⟩ => Matrix.of fun c c' => (Tgt.t8_145k0.getD c []).getD c' 0
  | ⟨53, _⟩ => Matrix.of fun c c' => (Tgt.t8_146k0.getD c []).getD c' 0
  | ⟨54, _⟩ => Matrix.of fun c c' => (Tgt.t8_155k0.getD c []).getD c' 0
  | ⟨55, _⟩ => Matrix.of fun c c' => (Tgt.t8_155k1.getD c []).getD c' 0
  | ⟨56, _⟩ => Matrix.of fun c c' => (Tgt.t8_156k0.getD c []).getD c' 0
  | ⟨57, _⟩ => Matrix.of fun c c' => (Tgt.t8_166k0.getD c []).getD c' 0
  | ⟨58, _⟩ => Matrix.of fun c c' => (Tgt.t8_166k1.getD c []).getD c' 0
  | ⟨59, _⟩ => Matrix.of fun c c' => (Tgt.t8_222k0.getD c []).getD c' 0
  | ⟨60, _⟩ => Matrix.of fun c c' => (Tgt.t8_222k2.getD c []).getD c' 0
  | ⟨61, _⟩ => Matrix.of fun c c' => (Tgt.t8_223k0.getD c []).getD c' 0
  | ⟨62, _⟩ => Matrix.of fun c c' => (Tgt.t8_223k1.getD c []).getD c' 0
  | ⟨63, _⟩ => Matrix.of fun c c' => (Tgt.t8_224k0.getD c []).getD c' 0
  | ⟨64, _⟩ => Matrix.of fun c c' => (Tgt.t8_224k1.getD c []).getD c' 0
  | ⟨65, _⟩ => Matrix.of fun c c' => (Tgt.t8_225k0.getD c []).getD c' 0
  | ⟨66, _⟩ => Matrix.of fun c c' => (Tgt.t8_225k1.getD c []).getD c' 0
  | ⟨67, _⟩ => Matrix.of fun c c' => (Tgt.t8_226k0.getD c []).getD c' 0
  | ⟨68, _⟩ => Matrix.of fun c c' => (Tgt.t8_226k1.getD c []).getD c' 0
  | ⟨69, _⟩ => Matrix.of fun c c' => (Tgt.t8_233k0.getD c []).getD c' 0
  | ⟨70, _⟩ => Matrix.of fun c c' => (Tgt.t8_233k1.getD c []).getD c' 0
  | ⟨71, _⟩ => Matrix.of fun c c' => (Tgt.t8_234k0.getD c []).getD c' 0
  | ⟨72, _⟩ => Matrix.of fun c c' => (Tgt.t8_235k0.getD c []).getD c' 0
  | ⟨73, _⟩ => Matrix.of fun c c' => (Tgt.t8_236k0.getD c []).getD c' 0
  | ⟨74, _⟩ => Matrix.of fun c c' => (Tgt.t8_244k0.getD c []).getD c' 0
  | ⟨75, _⟩ => Matrix.of fun c c' => (Tgt.t8_244k1.getD c []).getD c' 0
  | ⟨76, _⟩ => Matrix.of fun c c' => (Tgt.t8_245k0.getD c []).getD c' 0
  | ⟨77, _⟩ => Matrix.of fun c c' => (Tgt.t8_246k0.getD c []).getD c' 0
  | ⟨78, _⟩ => Matrix.of fun c c' => (Tgt.t8_255k0.getD c []).getD c' 0
  | ⟨79, _⟩ => Matrix.of fun c c' => (Tgt.t8_255k1.getD c []).getD c' 0
  | ⟨80, _⟩ => Matrix.of fun c c' => (Tgt.t8_256k0.getD c []).getD c' 0
  | ⟨81, _⟩ => Matrix.of fun c c' => (Tgt.t8_266k0.getD c []).getD c' 0
  | ⟨82, _⟩ => Matrix.of fun c c' => (Tgt.t8_266k1.getD c []).getD c' 0
  | ⟨83, _⟩ => Matrix.of fun c c' => (Tgt.t8_333k0.getD c []).getD c' 0
  | ⟨84, _⟩ => Matrix.of fun c c' => (Tgt.t8_333k2.getD c []).getD c' 0
  | ⟨85, _⟩ => Matrix.of fun c c' => (Tgt.t8_334k0.getD c []).getD c' 0
  | ⟨86, _⟩ => Matrix.of fun c c' => (Tgt.t8_334k1.getD c []).getD c' 0
  | ⟨87, _⟩ => Matrix.of fun c c' => (Tgt.t8_335k0.getD c []).getD c' 0
  | ⟨88, _⟩ => Matrix.of fun c c' => (Tgt.t8_335k1.getD c []).getD c' 0
  | ⟨89, _⟩ => Matrix.of fun c c' => (Tgt.t8_336k0.getD c []).getD c' 0
  | ⟨90, _⟩ => Matrix.of fun c c' => (Tgt.t8_336k1.getD c []).getD c' 0
  | ⟨91, _⟩ => Matrix.of fun c c' => (Tgt.t8_344k0.getD c []).getD c' 0
  | ⟨92, _⟩ => Matrix.of fun c c' => (Tgt.t8_344k1.getD c []).getD c' 0
  | ⟨93, _⟩ => Matrix.of fun c c' => (Tgt.t8_345k0.getD c []).getD c' 0
  | ⟨94, _⟩ => Matrix.of fun c c' => (Tgt.t8_346k0.getD c []).getD c' 0
  | ⟨95, _⟩ => Matrix.of fun c c' => (Tgt.t8_355k0.getD c []).getD c' 0
  | ⟨96, _⟩ => Matrix.of fun c c' => (Tgt.t8_355k1.getD c []).getD c' 0
  | ⟨97, _⟩ => Matrix.of fun c c' => (Tgt.t8_356k0.getD c []).getD c' 0
  | ⟨98, _⟩ => Matrix.of fun c c' => (Tgt.t8_366k0.getD c []).getD c' 0
  | ⟨99, _⟩ => Matrix.of fun c c' => (Tgt.t8_366k1.getD c []).getD c' 0
  | ⟨100, _⟩ => Matrix.of fun c c' => (Tgt.t8_444k0.getD c []).getD c' 0
  | ⟨101, _⟩ => Matrix.of fun c c' => (Tgt.t8_444k1.getD c []).getD c' 0
  | ⟨102, _⟩ => Matrix.of fun c c' => (Tgt.t8_444k2.getD c []).getD c' 0
  | ⟨103, _⟩ => Matrix.of fun c c' => (Tgt.t8_445k0.getD c []).getD c' 0
  | ⟨104, _⟩ => Matrix.of fun c c' => (Tgt.t8_445k1.getD c []).getD c' 0
  | ⟨105, _⟩ => Matrix.of fun c c' => (Tgt.t8_446k0.getD c []).getD c' 0
  | ⟨106, _⟩ => Matrix.of fun c c' => (Tgt.t8_446k1.getD c []).getD c' 0
  | ⟨107, _⟩ => Matrix.of fun c c' => (Tgt.t8_455k0.getD c []).getD c' 0
  | ⟨108, _⟩ => Matrix.of fun c c' => (Tgt.t8_455k1.getD c []).getD c' 0
  | ⟨109, _⟩ => Matrix.of fun c c' => (Tgt.t8_456k0.getD c []).getD c' 0
  | ⟨110, _⟩ => Matrix.of fun c c' => (Tgt.t8_466k0.getD c []).getD c' 0
  | ⟨111, _⟩ => Matrix.of fun c c' => (Tgt.t8_466k1.getD c []).getD c' 0
  | ⟨112, _⟩ => Matrix.of fun c c' => (Tgt.t8_555k0.getD c []).getD c' 0
  | ⟨113, _⟩ => Matrix.of fun c c' => (Tgt.t8_555k1.getD c []).getD c' 0
  | ⟨114, _⟩ => Matrix.of fun c c' => (Tgt.t8_555k2.getD c []).getD c' 0
  | ⟨115, _⟩ => Matrix.of fun c c' => (Tgt.t8_556k0.getD c []).getD c' 0
  | ⟨116, _⟩ => Matrix.of fun c c' => (Tgt.t8_556k1.getD c []).getD c' 0
  | ⟨117, _⟩ => Matrix.of fun c c' => (Tgt.t8_566k0.getD c []).getD c' 0
  | ⟨118, _⟩ => Matrix.of fun c c' => (Tgt.t8_566k1.getD c []).getD c' 0
  | ⟨119, _⟩ => Matrix.of fun c c' => (Tgt.t8_666k0.getD c []).getD c' 0
  | ⟨120, _⟩ => Matrix.of fun c c' => (Tgt.t8_666k1.getD c []).getD c' 0
  | ⟨121, _⟩ => Matrix.of fun c c' => (Tgt.t8_666k2.getD c []).getD c' 0
  | ⟨k + 122, h⟩ => False.elim (by have h122 : x2NumKeys 0 = 122 := rfl; omega)

/-- The target of every h block for the concrete data. -/
theorem x2Target_concrete : ∀ b : x2Key 0,
    x2Target x2DataConcrete b = Matrix.of fun (c c' : x2Col 0 b) => ((x2TgtLit b c c' : ℤ) : ℚ) / 8
  | ⟨0, _⟩ => Tgt.tgt_003k0
  | ⟨1, _⟩ => Tgt.tgt_004k0
  | ⟨2, _⟩ => Tgt.tgt_005k0
  | ⟨3, _⟩ => Tgt.tgt_011k0
  | ⟨4, _⟩ => Tgt.tgt_012k0
  | ⟨5, _⟩ => Tgt.tgt_013k0
  | ⟨6, _⟩ => Tgt.tgt_014k0
  | ⟨7, _⟩ => Tgt.tgt_015k0
  | ⟨8, _⟩ => Tgt.tgt_016k0
  | ⟨9, _⟩ => Tgt.tgt_022k0
  | ⟨10, _⟩ => Tgt.tgt_023k0
  | ⟨11, _⟩ => Tgt.tgt_024k0
  | ⟨12, _⟩ => Tgt.tgt_025k0
  | ⟨13, _⟩ => Tgt.tgt_026k0
  | ⟨14, _⟩ => Tgt.tgt_033k0
  | ⟨15, _⟩ => Tgt.tgt_034k0
  | ⟨16, _⟩ => Tgt.tgt_035k0
  | ⟨17, _⟩ => Tgt.tgt_036k0
  | ⟨18, _⟩ => Tgt.tgt_044k0
  | ⟨19, _⟩ => Tgt.tgt_044k1
  | ⟨20, _⟩ => Tgt.tgt_045k0
  | ⟨21, _⟩ => Tgt.tgt_046k0
  | ⟨22, _⟩ => Tgt.tgt_055k0
  | ⟨23, _⟩ => Tgt.tgt_055k1
  | ⟨24, _⟩ => Tgt.tgt_056k0
  | ⟨25, _⟩ => Tgt.tgt_066k0
  | ⟨26, _⟩ => Tgt.tgt_066k1
  | ⟨27, _⟩ => Tgt.tgt_111k0
  | ⟨28, _⟩ => Tgt.tgt_111k2
  | ⟨29, _⟩ => Tgt.tgt_112k0
  | ⟨30, _⟩ => Tgt.tgt_112k1
  | ⟨31, _⟩ => Tgt.tgt_113k0
  | ⟨32, _⟩ => Tgt.tgt_113k1
  | ⟨33, _⟩ => Tgt.tgt_114k0
  | ⟨34, _⟩ => Tgt.tgt_114k1
  | ⟨35, _⟩ => Tgt.tgt_115k0
  | ⟨36, _⟩ => Tgt.tgt_115k1
  | ⟨37, _⟩ => Tgt.tgt_116k0
  | ⟨38, _⟩ => Tgt.tgt_116k1
  | ⟨39, _⟩ => Tgt.tgt_122k0
  | ⟨40, _⟩ => Tgt.tgt_122k1
  | ⟨41, _⟩ => Tgt.tgt_123k0
  | ⟨42, _⟩ => Tgt.tgt_124k0
  | ⟨43, _⟩ => Tgt.tgt_125k0
  | ⟨44, _⟩ => Tgt.tgt_126k0
  | ⟨45, _⟩ => Tgt.tgt_133k0
  | ⟨46, _⟩ => Tgt.tgt_133k1
  | ⟨47, _⟩ => Tgt.tgt_134k0
  | ⟨48, _⟩ => Tgt.tgt_135k0
  | ⟨49, _⟩ => Tgt.tgt_136k0
  | ⟨50, _⟩ => Tgt.tgt_144k0
  | ⟨51, _⟩ => Tgt.tgt_144k1
  | ⟨52, _⟩ => Tgt.tgt_145k0
  | ⟨53, _⟩ => Tgt.tgt_146k0
  | ⟨54, _⟩ => Tgt.tgt_155k0
  | ⟨55, _⟩ => Tgt.tgt_155k1
  | ⟨56, _⟩ => Tgt.tgt_156k0
  | ⟨57, _⟩ => Tgt.tgt_166k0
  | ⟨58, _⟩ => Tgt.tgt_166k1
  | ⟨59, _⟩ => Tgt.tgt_222k0
  | ⟨60, _⟩ => Tgt.tgt_222k2
  | ⟨61, _⟩ => Tgt.tgt_223k0
  | ⟨62, _⟩ => Tgt.tgt_223k1
  | ⟨63, _⟩ => Tgt.tgt_224k0
  | ⟨64, _⟩ => Tgt.tgt_224k1
  | ⟨65, _⟩ => Tgt.tgt_225k0
  | ⟨66, _⟩ => Tgt.tgt_225k1
  | ⟨67, _⟩ => Tgt.tgt_226k0
  | ⟨68, _⟩ => Tgt.tgt_226k1
  | ⟨69, _⟩ => Tgt.tgt_233k0
  | ⟨70, _⟩ => Tgt.tgt_233k1
  | ⟨71, _⟩ => Tgt.tgt_234k0
  | ⟨72, _⟩ => Tgt.tgt_235k0
  | ⟨73, _⟩ => Tgt.tgt_236k0
  | ⟨74, _⟩ => Tgt.tgt_244k0
  | ⟨75, _⟩ => Tgt.tgt_244k1
  | ⟨76, _⟩ => Tgt.tgt_245k0
  | ⟨77, _⟩ => Tgt.tgt_246k0
  | ⟨78, _⟩ => Tgt.tgt_255k0
  | ⟨79, _⟩ => Tgt.tgt_255k1
  | ⟨80, _⟩ => Tgt.tgt_256k0
  | ⟨81, _⟩ => Tgt.tgt_266k0
  | ⟨82, _⟩ => Tgt.tgt_266k1
  | ⟨83, _⟩ => Tgt.tgt_333k0
  | ⟨84, _⟩ => Tgt.tgt_333k2
  | ⟨85, _⟩ => Tgt.tgt_334k0
  | ⟨86, _⟩ => Tgt.tgt_334k1
  | ⟨87, _⟩ => Tgt.tgt_335k0
  | ⟨88, _⟩ => Tgt.tgt_335k1
  | ⟨89, _⟩ => Tgt.tgt_336k0
  | ⟨90, _⟩ => Tgt.tgt_336k1
  | ⟨91, _⟩ => Tgt.tgt_344k0
  | ⟨92, _⟩ => Tgt.tgt_344k1
  | ⟨93, _⟩ => Tgt.tgt_345k0
  | ⟨94, _⟩ => Tgt.tgt_346k0
  | ⟨95, _⟩ => Tgt.tgt_355k0
  | ⟨96, _⟩ => Tgt.tgt_355k1
  | ⟨97, _⟩ => Tgt.tgt_356k0
  | ⟨98, _⟩ => Tgt.tgt_366k0
  | ⟨99, _⟩ => Tgt.tgt_366k1
  | ⟨100, _⟩ => Tgt.tgt_444k0
  | ⟨101, _⟩ => Tgt.tgt_444k1
  | ⟨102, _⟩ => Tgt.tgt_444k2
  | ⟨103, _⟩ => Tgt.tgt_445k0
  | ⟨104, _⟩ => Tgt.tgt_445k1
  | ⟨105, _⟩ => Tgt.tgt_446k0
  | ⟨106, _⟩ => Tgt.tgt_446k1
  | ⟨107, _⟩ => Tgt.tgt_455k0
  | ⟨108, _⟩ => Tgt.tgt_455k1
  | ⟨109, _⟩ => Tgt.tgt_456k0
  | ⟨110, _⟩ => Tgt.tgt_466k0
  | ⟨111, _⟩ => Tgt.tgt_466k1
  | ⟨112, _⟩ => Tgt.tgt_555k0
  | ⟨113, _⟩ => Tgt.tgt_555k1
  | ⟨114, _⟩ => Tgt.tgt_555k2
  | ⟨115, _⟩ => Tgt.tgt_556k0
  | ⟨116, _⟩ => Tgt.tgt_556k1
  | ⟨117, _⟩ => Tgt.tgt_566k0
  | ⟨118, _⟩ => Tgt.tgt_566k1
  | ⟨119, _⟩ => Tgt.tgt_666k0
  | ⟨120, _⟩ => Tgt.tgt_666k1
  | ⟨121, _⟩ => Tgt.tgt_666k2
  | ⟨k + 122, h⟩ => False.elim (by have h122 : x2NumKeys 0 = 122 := rfl; omega)

end ThreeCopyQutritWerner.X2
