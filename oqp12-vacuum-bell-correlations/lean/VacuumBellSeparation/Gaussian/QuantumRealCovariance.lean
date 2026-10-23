module

public import VacuumBellSeparation.Gaussian.QuantumModePositivity

@[expose] public section


/-!
# Real positive covariance from actual strict quantum uncertainty

The real part of V+iΩ/2 is literally V. Testing the actual complex
positive matrix on embedded real vectors proves positive definiteness of
V. This is an elementary direction of the uncertainty condition, not an
inference of uncertainty from an arbitrary state or formal kernel.
-/

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix
open scoped ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[simp] theorem quantumCovariance_re_apply (V Ω : Matrix ι ι ℝ) (i j : ι) :
    (quantumCovariance V Ω i j).re = V i j := by
  simp [quantumCovariance, Complex.mul_re, Complex.div_re, Complex.div_im]

theorem real_isHermitian_of_quantum_isHermitian {V Ω : Matrix ι ι ℝ}
    (hQ : (quantumCovariance V Ω).IsHermitian) : V.IsHermitian := by
  change Vᵀ = V
  ext i j
  have h := congrArg Complex.re (congrFun (congrFun hQ.eq i) j)
  simpa only [Matrix.conjTranspose_apply, Complex.star_def, Complex.conj_re,
    quantumCovariance_re_apply, Matrix.transpose_apply] using h

theorem real_quantum_quadratic (V Ω : Matrix ι ι ℝ) (x : ι → ℝ) :
    (star (fun i => (x i : ℂ)) ⬝ᵥ
      (quantumCovariance V Ω *ᵥ (fun i => (x i : ℂ)))).re = x ⬝ᵥ (V *ᵥ x) := by
  simp [dotProduct, Matrix.mulVec, Complex.mul_re, Complex.mul_im]

theorem real_posDef_of_quantum_posDef {V Ω : Matrix ι ι ℝ}
    (hQ : (quantumCovariance V Ω).PosDef) : V.PosDef := by
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  refine ⟨real_isHermitian_of_quantum_isHermitian hQ.isHermitian, ?_⟩
  intro x hx
  have hxc : (fun i => (x i : ℂ)) ≠ 0 := by
    intro he
    apply hx
    funext i
    have h := congrArg Complex.re (congrFun he i)
    simpa using h
  have h := (Complex.pos_iff.mp (hQ.dotProduct_mulVec_pos hxc)).1
  rw [real_quantum_quadratic] at h
  simpa only [star_trivial] using h

theorem quantum_covariance_shift_posDef {V Ω : Matrix ι ι ℝ}
    (hQ : (quantumCovariance V Ω).PosDef) : (V + (1 / 2 : ℝ) • 1).PosDef :=
  (real_posDef_of_quantum_posDef hQ).add_posSemidef
    (Matrix.PosSemidef.one.smul (by norm_num : (0 : ℝ) ≤ 1 / 2))

end VacuumBellSeparation.Gaussian
