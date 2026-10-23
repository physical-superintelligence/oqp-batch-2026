module

public import ThreeCopyQutritWerner.CertificateDescendantSourceSizes
public import ThreeCopyQutritWerner.CertificateLocalFrameMetrics

@[expose] public section


noncomputable section
open scoped BigOperators Matrix ComplexOrder
namespace ThreeCopyQutritWerner

/-- The original archive Gram matrix of each source type. -/
def certificateLocalDecomposition0Gram : (t : Fin 7) → Matrix (Fin (certificateDescendantFrames2SourceSize t)) (Fin (certificateDescendantFrames2SourceSize t)) ℂ := by
  exact
    Fin.cases (certificateLocalGram0_0.map (Int.cast : ℤ → ℂ)) <|
    Fin.cases (certificateLocalGram0_1.map (Int.cast : ℤ → ℂ)) <|
    Fin.cases (certificateLocalGram0_2.map (Int.cast : ℤ → ℂ)) <|
    Fin.cases (certificateLocalGram0_3.map (Int.cast : ℤ → ℂ)) <|
    Fin.cases (certificateLocalGram0_4.map (Int.cast : ℤ → ℂ)) <|
    Fin.cases (certificateLocalGram0_5.map (Int.cast : ℤ → ℂ)) <|
    Fin.cases (certificateLocalGram0_6.map (Int.cast : ℤ → ℂ)) <|
    Fin.rec0

theorem certificateLocalDecomposition0Gram_posDef (t : Fin 7) :
    (certificateLocalDecomposition0Gram t).PosDef := by
  fin_cases t
  · exact certificateLocalGram0_0_posDef
  · exact certificateLocalGram0_1_posDef
  · exact certificateLocalGram0_2_posDef
  · exact certificateLocalGram0_3_posDef
  · exact certificateLocalGram0_4_posDef
  · exact certificateLocalGram0_5_posDef
  · exact certificateLocalGram0_6_posDef

/-- The original archive Gram matrix of each source type. -/
def certificateLocalDecomposition1Gram : (t : Fin 8) → Matrix (Fin (certificateDescendantFrames1SourceSize t)) (Fin (certificateDescendantFrames1SourceSize t)) ℂ := by
  exact
    Fin.cases (certificateLocalGram1_0.map (Int.cast : ℤ → ℂ)) <|
    Fin.cases (certificateLocalGram1_1.map (Int.cast : ℤ → ℂ)) <|
    Fin.cases (certificateLocalGram1_2.map (Int.cast : ℤ → ℂ)) <|
    Fin.cases (certificateLocalGram1_3.map (Int.cast : ℤ → ℂ)) <|
    Fin.cases (certificateLocalGram1_4.map (Int.cast : ℤ → ℂ)) <|
    Fin.cases (certificateLocalGram1_5.map (Int.cast : ℤ → ℂ)) <|
    Fin.cases (certificateLocalGram1_6.map (Int.cast : ℤ → ℂ)) <|
    Fin.cases (certificateLocalGram1_7.map (Int.cast : ℤ → ℂ)) <|
    Fin.rec0

theorem certificateLocalDecomposition1Gram_posDef (t : Fin 8) :
    (certificateLocalDecomposition1Gram t).PosDef := by
  fin_cases t
  · exact certificateLocalGram1_0_posDef
  · exact certificateLocalGram1_1_posDef
  · exact certificateLocalGram1_2_posDef
  · exact certificateLocalGram1_3_posDef
  · exact certificateLocalGram1_4_posDef
  · exact certificateLocalGram1_5_posDef
  · exact certificateLocalGram1_6_posDef
  · exact certificateLocalGram1_7_posDef

end ThreeCopyQutritWerner
