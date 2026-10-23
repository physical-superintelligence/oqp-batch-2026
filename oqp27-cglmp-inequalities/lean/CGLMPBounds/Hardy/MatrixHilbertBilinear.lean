module

public import CGLMPBounds.Hardy.CircleMatrixParseval

@[expose] public section


/-! Bilinear trace skew-symmetry and finite linearity of the actual Hilbert
transform. These identities keep the noncommutative matrix multiplication
inside the trace. -/
namespace CGLMPBounds.Hardy
open MeasureTheory Matrix
open scoped ComplexConjugate Matrix.Norms.Elementwise
noncomputable section
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance {r : ℕ} : ENormedAddMonoid (Circulation.Mat r) :=
  inferInstanceAs (ENormedAddMonoid (Fin r → Fin r → ℂ))

 theorem scalarHilbert_bilinear_skew (f g : UnitCircle → ℂ)
    (hf : MemLp f 2 circleMeasure) (hg : MemLp g 2 circleMeasure) :
    (∫ t, f t * scalarHilbert g t ∂circleMeasure) =
      -(∫ t, scalarHilbert f t * g t ∂circleMeasure) := by
  have hfc : MemLp (fun t => conj (f t)) 2 circleMeasure := by
    have he : star f = (fun t => conj (f t)) := rfl
    simpa only [he] using hf.star
  have h := scalarHilbert_skewAdjoint (fun t => conj (f t)) g hfc hg
  simp only [Complex.conj_conj] at h
  rw [h]
  congr 1
  apply integral_congr_ae
  filter_upwards [scalarHilbert_conj f hf] with t ht
  rw [ht, Complex.conj_conj]

theorem scalar_circle_mul_integrable (f g : UnitCircle → ℂ)
    (hf : MemLp f 2 circleMeasure) (hg : MemLp g 2 circleMeasure) :
    Integrable (fun t => f t*g t) circleMeasure := by
  have h : MemLp (f*g) 1 circleMeasure := hf.mul hg
  exact memLp_one_iff_integrable.mp h

theorem matrix_circle_trace_mul_integrable {r : ℕ} (F G : UnitCircle → Circulation.Mat r)
    (hF : MemLp F 2 circleMeasure) (hG : MemLp G 2 circleMeasure) :
    Integrable (fun t => Circulation.tr (F t*G t)) circleMeasure := by
  simp only [Circulation.tr, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  apply Integrable.div_const
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  exact scalar_circle_mul_integrable _ _ ((hF.eval i).eval j) ((hG.eval j).eval i)

theorem matrix_circle_integral_trace_mul {r : ℕ} (F G : UnitCircle → Circulation.Mat r)
    (hF : MemLp F 2 circleMeasure) (hG : MemLp G 2 circleMeasure) :
    (∫ t, Circulation.tr (F t*G t) ∂circleMeasure) =
      (∑ i, ∑ j, ∫ t, F t i j*G t j i ∂circleMeasure)/(r : ℂ) := by
  simp only [Circulation.tr, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  rw [integral_div]
  rw [integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum _ (fun j _ =>
    scalar_circle_mul_integrable _ _ ((hF.eval i).eval j) ((hG.eval j).eval i)))]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum Finset.univ (fun j _ =>
    scalar_circle_mul_integrable _ _ ((hF.eval i).eval j) ((hG.eval j).eval i))]

theorem matrixHilbert_bilinear_skew {r : ℕ} (F G : UnitCircle → Circulation.Mat r)
    (hF : MemLp F 2 circleMeasure) (hG : MemLp G 2 circleMeasure) :
    (∫ t, Circulation.tr (F t*matrixHilbert G t) ∂circleMeasure) =
      -(∫ t, Circulation.tr (matrixHilbert F t*G t) ∂circleMeasure) := by
  rw [matrix_circle_integral_trace_mul _ _ hF (matrixHilbert_memLp G),
    matrix_circle_integral_trace_mul _ _ (matrixHilbert_memLp F) hG]
  simp only [matrixHilbert, scalarHilbert_bilinear_skew _ _
    ((hF.eval _).eval _) ((hG.eval _).eval _), Finset.sum_neg_distrib, neg_div]

theorem matrixHilbert_bilinear_cross {r : ℕ} (F G : UnitCircle → Circulation.Mat r)
    (hF : MemLp F 2 circleMeasure) (hG : MemLp G 2 circleMeasure) :
    (∫ t, Circulation.tr (G t*matrixHilbert F t) ∂circleMeasure) =
      -(∫ t, Circulation.tr (F t*matrixHilbert G t) ∂circleMeasure) := by
  rw [matrixHilbert_bilinear_skew _ _ hG hF]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  exact congrArg (fun z : ℂ => z/(r : ℂ)) (Matrix.trace_mul_comm _ _)

theorem matrixHilbert_bilinear_self {r : ℕ} (F : UnitCircle → Circulation.Mat r)
    (hF : MemLp F 2 circleMeasure) :
    (∫ t, Circulation.tr (F t*matrixHilbert F t) ∂circleMeasure) = 0 := by
  have h := matrixHilbert_bilinear_cross F F hF hF
  linear_combination (1/2 : ℂ)*h

theorem matrixHilbert_linearCombination {r : ℕ} (F G : UnitCircle → Circulation.Mat r)
    (hF : MemLp F 2 circleMeasure) (hG : MemLp G 2 circleMeasure) (a b : ℂ) :
    matrixHilbert (fun t => a • F t + b • G t) =ᵐ[circleMeasure]
      fun t => a • matrixHilbert F t + b • matrixHilbert G t := by
  have hs : ∀ i j : Fin r, ∀ᵐ t ∂circleMeasure,
      scalarHilbert (fun s => a*F s i j+b*G s i j) t =
        a*scalarHilbert (fun s => F s i j) t+b*scalarHilbert (fun s => G s i j) t := by
    intro i j
    filter_upwards [scalarHilbert_add (fun s => a*F s i j) (fun s => b*G s i j)
      (((hF.eval i).eval j).const_smul a) (((hG.eval i).eval j).const_smul b),
      scalarHilbert_const_mul (fun s => F s i j) ((hF.eval i).eval j) a,
      scalarHilbert_const_mul (fun s => G s i j) ((hG.eval i).eval j) b] with t ht ha hb
    rw [ht, ha, hb]
  simp only [← Filter.eventually_all] at hs
  filter_upwards [hs] with t ht
  ext i j
  exact ht i j

theorem matrixHilbert_congr {r : ℕ} {F G : UnitCircle → Circulation.Mat r}
    (hFG : F = G) : matrixHilbert F = matrixHilbert G := by rw [hFG]

end
end CGLMPBounds.Hardy
