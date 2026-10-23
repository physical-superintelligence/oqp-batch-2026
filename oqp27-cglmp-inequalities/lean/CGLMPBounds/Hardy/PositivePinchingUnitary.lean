module

public import CGLMPBounds.Hardy.PositivePinchingDiagonal

@[expose] public section


/-! Actual unitary covariance of the C.4 definitions and diagonalization of
a Hermitian involution. No invariance of the density or measure is assumed. -/

namespace CGLMPBounds.Hardy
noncomputable section
open Matrix Unitary
open scoped Polynomial
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma charpoly_conjStarAlgAut (U : unitary (Matrix ι ι ℂ)) (A : Matrix ι ι ℂ) :
    (conjStarAlgAut ℂ _ U A).charpoly = A.charpoly := by
  rw [conjStarAlgAut_apply, Matrix.charpoly_mul_comm, ← mul_assoc]
  simp

lemma trace_conjStarAlgAut (U : unitary (Matrix ι ι ℂ)) (A : Matrix ι ι ℂ) :
    Matrix.trace (conjStarAlgAut ℂ _ U A) = Matrix.trace A := by
  exact Matrix.trace_units_conj (Unitary.toUnits U) A

theorem positivePinching_part_conjStarAlgAut (U : unitary (Matrix ι ι ℂ))
    (B Y : Matrix ι ι ℂ) :
    positivePinchingPart (conjStarAlgAut ℂ _ U B) (conjStarAlgAut ℂ _ U Y) =
      conjStarAlgAut ℂ _ U (positivePinchingPart B Y) := by
  simp only [positivePinchingPart, map_smul, map_add, map_mul]

theorem positivePinching_offdiag_conjStarAlgAut (U : unitary (Matrix ι ι ℂ))
    (B Y : Matrix ι ι ℂ) :
    positivePinchingOffdiag (conjStarAlgAut ℂ _ U B) (conjStarAlgAut ℂ _ U Y) =
      conjStarAlgAut ℂ _ U (positivePinchingOffdiag B Y) := by
  simp only [positivePinchingOffdiag, map_sub, positivePinching_part_conjStarAlgAut]

theorem positivePinching_omega_conjStarAlgAut (U : unitary (Matrix ι ι ℂ))
    (B Y : Matrix ι ι ℂ) (x y : ℝ) :
    positivePinchingOmega (conjStarAlgAut ℂ _ U B) (conjStarAlgAut ℂ _ U Y) x y =
      positivePinchingOmega B Y x y := by
  unfold positivePinchingOmega
  have hp : (conjStarAlgAut ℂ _ U B - (x : ℂ) • (1 : Matrix ι ι ℂ)) *
      (conjStarAlgAut ℂ _ U Y - (y : ℂ) • 1) =
      conjStarAlgAut ℂ _ U ((B - (x : ℂ) • 1) * (Y - (y : ℂ) • 1)) := by
    simp only [map_mul, map_sub, map_smul, map_one]
  rw [hp, charpoly_conjStarAlgAut]

theorem positivePinching_density_conjStarAlgAut (U : unitary (Matrix ι ι ℂ))
    (B Y : Matrix ι ι ℂ) :
    positivePinchingDensity (conjStarAlgAut ℂ _ U B) (conjStarAlgAut ℂ _ U Y) =
      positivePinchingDensity B Y := by
  funext p
  simp only [positivePinchingDensity, positivePinching_omega_conjStarAlgAut]

theorem positivePinching_measure_conjStarAlgAut (U : unitary (Matrix ι ι ℂ))
    (B Y : Matrix ι ι ℂ) :
    positivePinchingMeasure (conjStarAlgAut ℂ _ U B) (conjStarAlgAut ℂ _ U Y) =
      positivePinchingMeasure B Y := by
  simp only [positivePinchingMeasure, positivePinching_density_conjStarAlgAut]

theorem positivePinching_offdiag_sq_trace_conjStarAlgAut (U : unitary (Matrix ι ι ℂ))
    (B Y : Matrix ι ι ℂ) :
    Matrix.trace (positivePinchingOffdiag (conjStarAlgAut ℂ _ U B)
      (conjStarAlgAut ℂ _ U Y) ^ 2) = Matrix.trace (positivePinchingOffdiag B Y ^ 2) := by
  rw [positivePinching_offdiag_conjStarAlgAut, ← map_pow, trace_conjStarAlgAut]

theorem normalizedPolynomialTrace_conjStarAlgAut (U : unitary (Matrix ι ι ℂ))
    (f : ℂ[X]) (A : Matrix ι ι ℂ) :
    normalizedPolynomialTrace f (conjStarAlgAut ℂ _ U A) = normalizedPolynomialTrace f A := by
  unfold normalizedPolynomialTrace
  have hs : (∑ k ∈ f.support, (f.coeff k) • conjStarAlgAut ℂ _ U A ^ k) =
      conjStarAlgAut ℂ _ U (∑ k ∈ f.support, (f.coeff k) • A ^ k) := by
    simp only [map_sum, map_smul, map_pow]
  rw [hs, trace_conjStarAlgAut]

theorem hermitian_involution_exists_sign_diagonal {B : Matrix ι ι ℂ}
    (hB : B.IsHermitian) (hB2 : B ^ 2 = 1) :
    ∃ (U : unitary (Matrix ι ι ℂ)) (σ : ι → Bool),
      B = conjStarAlgAut ℂ _ U (involutionFromSigns σ) := by
  have hd2 := congrArg (conjStarAlgAut ℂ _ (star hB.eigenvectorUnitary)) hB2
  rw [map_pow, hB.conjStarAlgAut_star_eigenvectorUnitary, map_one] at hd2
  have hsign (i : ι) : hB.eigenvalues i = 1 ∨ hB.eigenvalues i = -1 := by
    have hi := congrArg (fun A : Matrix ι ι ℂ => A i i) hd2
    have hiC : ((hB.eigenvalues i : ℝ) : ℂ) ^ 2 = 1 := by
      simpa only [pow_two, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq,
        Matrix.one_apply_eq, Function.comp_apply, RCLike.ofReal_eq_complex_ofReal] using hi
    have hiR : hB.eigenvalues i ^ 2 = 1 := by exact_mod_cast hiC
    exact (sq_eq_one_iff).mp hiR
  let σ : ι → Bool := fun i => decide (hB.eigenvalues i = 1)
  refine ⟨hB.eigenvectorUnitary, σ, ?_⟩
  conv_lhs => rw [hB.spectral_theorem]
  congr 1
  unfold involutionFromSigns
  congr 1
  funext i
  rcases hsign i with hi | hi <;> simp [σ, hi]
  all_goals norm_num

end
end CGLMPBounds.Hardy
