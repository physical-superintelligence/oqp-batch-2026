module

public import CGLMPBounds.Hardy.MatrixHermitianParts

@[expose] public section


/-! Coordinate and real-part integration maps in the actual Hilbert
operator-norm matrix space. The scalar-entry definition of the Poisson
integral is thereby independent of any alternative equivalent matrix norm. -/
namespace CGLMPBounds.Hardy
noncomputable section
open Matrix MeasureTheory
open scoped Matrix.Norms.L2Operator
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

def matrixEntryLinearMap {r : ℕ} (i j : Fin r) : Circulation.Mat r →ₗ[ℂ] ℂ :=
  (LinearMap.proj j : (Fin r → ℂ) →ₗ[ℂ] ℂ).comp
    (LinearMap.proj i : (Fin r → Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ))

def matrixEntryCLM {r : ℕ} (i j : Fin r) : Circulation.Mat r →L[ℂ] ℂ :=
  (matrixEntryLinearMap i j).toContinuousLinearMap

@[simp] lemma matrixEntryCLM_apply {r : ℕ} (i j : Fin r) (X : Circulation.Mat r) :
    matrixEntryCLM i j X = X i j := rfl

lemma matrix_integral_entry {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {r : ℕ} {F : α → Circulation.Mat r} (hF : Integrable F μ) (i j : Fin r) :
    (∫ t, F t ∂μ) i j = ∫ t, F t i j ∂μ :=
  ((matrixEntryCLM i j).integral_comp_comm hF).symm

def hermitianRealPartLinearMap {r : ℕ} : Circulation.Mat r →ₗ[ℝ] Circulation.Mat r where
  toFun := hermitianRealPart
  map_add' X Y := by simp only [hermitianRealPart,conjTranspose_add]; module
  map_smul' a X := by
    ext i j
    simp [hermitianRealPart,Matrix.conjTranspose_apply,Complex.real_smul]
    ring

def hermitianRealPartCLM {r : ℕ} : Circulation.Mat r →L[ℝ] Circulation.Mat r :=
  hermitianRealPartLinearMap.toContinuousLinearMap

@[simp] lemma hermitianRealPartCLM_apply {r : ℕ} (X : Circulation.Mat r) :
    hermitianRealPartCLM X = hermitianRealPart X := rfl

lemma hermitianRealPart_integral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {r : ℕ} {F : α → Circulation.Mat r} (hF : Integrable F μ) :
    hermitianRealPart (∫ t, F t ∂μ) = ∫ t, hermitianRealPart (F t) ∂μ :=
  (hermitianRealPartCLM.integral_comp_comm hF).symm

lemma hermitianRealPart_smul_of_hermitian {r : ℕ} {B : Circulation.Mat r}
    (hB : B.IsHermitian) (z : ℂ) :
    hermitianRealPart (z • B) = (z.re : ℂ) • B := by
  simp only [hermitianRealPart,conjTranspose_smul,hB.eq]
  have he : z + star z = (2 : ℂ)*(z.re : ℂ) := by
    apply Complex.ext <;> simp <;> ring
  rw [← add_smul,smul_smul,he]
  congr 1
  ring

end
end CGLMPBounds.Hardy
