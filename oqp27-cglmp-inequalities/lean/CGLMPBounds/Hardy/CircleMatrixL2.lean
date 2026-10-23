module

public import CGLMPBounds.Hardy.CircularHilbertParseval
public import CGLMPBounds.Quantum.StochasticVariance
public import CGLMPBounds.Circulation.Core
public import Mathlib.MeasureTheory.SpecificCodomains.Pi

@[expose] public section


/-! Finite matrix entrywise L² and normalized Fourier identities for C.16.
All norms and traces retain the manuscript normalization. -/
namespace CGLMPBounds.Hardy
open MeasureTheory Matrix
open scoped ComplexConjugate Matrix.Norms.Elementwise
noncomputable section
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance {r : ℕ} : ENormedAddMonoid (Circulation.Mat r) :=
  inferInstanceAs (ENormedAddMonoid (Fin r → Fin r → ℂ))

 theorem matrix_conjTranspose_memLp {r : ℕ} (F : UnitCircle → Circulation.Mat r)
    (hF : MemLp F 2 circleMeasure) : MemLp (fun t => (F t)ᴴ) 2 circleMeasure := by
  apply MemLp.of_eval
  intro i
  apply MemLp.of_eval
  intro j
  have he : star (fun t => F t j i) = (fun t => conj (F t j i)) := rfl
  simpa only [he, Matrix.conjTranspose_apply, Complex.star_def] using
    ((hF.eval j).eval i).star

theorem matrixHilbert_memLp {r : ℕ} (F : UnitCircle → Circulation.Mat r) :
    MemLp (matrixHilbert F) 2 circleMeasure := by
  apply MemLp.of_eval
  intro i
  apply MemLp.of_eval
  intro j
  exact scalarHilbert_memLp (fun t => F t i j)

theorem matrix_integral_conjTranspose {r : ℕ} (F : UnitCircle → Circulation.Mat r)
    (hF : MemLp F 2 circleMeasure) :
    (∫ t, (F t)ᴴ ∂circleMeasure) = (∫ t, F t ∂circleMeasure)ᴴ := by
  have hi := hF.integrable (by norm_num)
  have hiH := (matrix_conjTranspose_memLp F hF).integrable (by norm_num)
  have hentry (G : UnitCircle → Circulation.Mat r) (hG : Integrable G circleMeasure)
      (i j : Fin r) : (∫ t, G t ∂circleMeasure) i j = ∫ t, G t i j ∂circleMeasure := by
    let L : Circulation.Mat r →L[ℂ] ℂ :=
      (ContinuousLinearMap.proj j : (Fin r → ℂ) →L[ℂ] ℂ).comp
        (ContinuousLinearMap.proj i : (Fin r → Fin r → ℂ) →L[ℂ] (Fin r → ℂ))
    simpa only [L, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
      using! (L.integral_comp_comm hG).symm
  ext i j
  calc
    _ = ∫ t, conj (F t j i) ∂circleMeasure := by
      simpa only [Matrix.conjTranspose_apply, Complex.star_def]
        using hentry (fun t => (F t)ᴴ) hiH i j
    _ = conj (∫ t, F t j i ∂circleMeasure) := integral_conj
    _ = _ := by
      simpa only [Matrix.conjTranspose_apply, Complex.star_def]
        using congrArg conj (hentry F hi j i).symm

theorem matrixCircleFourierCoefficient_apply {r : ℕ} (F : UnitCircle → Circulation.Mat r)
    (hF : Integrable F circleMeasure) (k : ℤ) (i j : Fin r) :
    matrixCircleFourierCoefficient F k i j = fourierCoeff (fun t => F t i j) k := by
  have hi := hF.fourier_smul (-k)
  let L : Circulation.Mat r →L[ℂ] ℂ :=
    (ContinuousLinearMap.proj j : (Fin r → ℂ) →L[ℂ] ℂ).comp
      (ContinuousLinearMap.proj i : (Fin r → Fin r → ℂ) →L[ℂ] (Fin r → ℂ))
  have he := L.integral_comp_comm hi
  simpa only [L, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    matrixCircleFourierCoefficient, fourierCoeff] using! he.symm

theorem matrixHilbert_conjTranspose {r : ℕ} (F : UnitCircle → Circulation.Mat r)
    (hF : MemLp F 2 circleMeasure) :
    matrixHilbert (fun t => (F t)ᴴ) =ᵐ[circleMeasure] fun t => (matrixHilbert F t)ᴴ := by
  have hs : ∀ i j : Fin r,
      scalarHilbert (fun t => conj (F t j i)) =ᵐ[circleMeasure]
        fun t => conj (scalarHilbert (fun s => F s j i) t) := by
    intro i j
    exact scalarHilbert_conj _ ((hF.eval j).eval i)
  simp only [Filter.EventuallyEq, ← Filter.eventually_all] at hs
  filter_upwards [hs] with t ht
  ext i j
  exact ht i j

theorem matrixHilbert_hermitian_ae {r : ℕ} (F : UnitCircle → Circulation.Mat r)
    (hF : MemLp F 2 circleMeasure) (hH : ∀ᵐ t ∂circleMeasure, (F t).IsHermitian) :
    ∀ᵐ t ∂circleMeasure, (matrixHilbert F t).IsHermitian := by
  have heq : (fun t => (F t)ᴴ) =ᵐ[circleMeasure] F := hH.mono (fun _ h => h.eq)
  have hHilb : matrixHilbert (fun t => (F t)ᴴ) = matrixHilbert F := by
    funext t i j
    exact congrFun (scalarHilbert_congr_ae _ _ (heq.mono (fun _ h => congrFun (congrFun h i) j))) t
  have h := matrixHilbert_conjTranspose F hF
  rw [hHilb] at h
  exact h.mono (fun _ ht => ht.symm)

theorem matrix_hsSq_eq_entry_norm_sq {r : ℕ} (X : Circulation.Mat r) :
    Circulation.hsSq X = (∑ i, ∑ j, ‖X i j‖^2)/(r : ℝ) := by
  rw [Circulation.hsSq, Circulation.reTr_eq, re_trace_gram_eq_sum_normSq]
  simp only [Complex.normSq_eq_norm_sq]

end
end CGLMPBounds.Hardy
