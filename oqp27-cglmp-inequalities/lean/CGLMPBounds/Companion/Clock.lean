module

public import CGLMPBounds.Defs.Companion

@[expose] public section


/-!
# Four-step clock algebra

For the convention `Σ_t |t⟩⟨t+1| ⊗ U_t` of supplement p. 6, the fourth power is
diagonal with the four oriented cyclic products. This finite identity is independent
of the source's construction of the transition matrices and of Fourier analysis.
-/

open Matrix
namespace CGLMPBounds.Companion
noncomputable section

section BlockRing
variable {R : Type*} [Ring R]

lemma weightedClock_sq (U : Fin 4 → R) :
    weightedClock U ^ 2 =
      Matrix.of (fun t s : Fin 4 => if s = t + 2 then U t * U (t + 1) else 0) := by
  rw [pow_two]
  ext t s
  fin_cases t <;> fin_cases s <;>
    norm_num [weightedClock, Matrix.mul_apply, Fin.sum_univ_four]

/-- The four diagonal blocks of the fourth clock power are the cyclic products. -/
theorem weightedClock_fourth (U : Fin 4 → R) :
    weightedClock U ^ 4 =
      Matrix.diagonal fun t => U t * U (t + 1) * U (t + 2) * U (t + 3) := by
  rw [show weightedClock U ^ 4 = weightedClock U ^ 2 * weightedClock U ^ 2 from
    pow_add (weightedClock U) 2 2, weightedClock_sq]
  ext t s
  fin_cases t <;> fin_cases s <;>
    norm_num [Matrix.mul_apply, Matrix.diagonal_apply, Fin.sum_univ_four, mul_assoc]

variable [StarRing R]

lemma weightedClock_star_mul (U : Fin 4 → R) (hU : ∀ t, star (U t) * U t = 1) :
    (weightedClock U)ᴴ * weightedClock U = 1 := by
  ext t s
  fin_cases t <;> fin_cases s <;>
    simp [weightedClock, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply, Fin.sum_univ_four, hU]

lemma weightedClock_mul_star (U : Fin 4 → R) (hU : ∀ t, U t * star (U t) = 1) :
    weightedClock U * (weightedClock U)ᴴ = 1 := by
  ext t s
  fin_cases t <;> fin_cases s <;>
    simp [weightedClock, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply, Fin.sum_univ_four, hU]

end BlockRing

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma clock_flatten_star (X : Matrix (Fin 4) (Fin 4) (Matrix ι ι ℂ)) :
    Matrix.compRingEquiv (Fin 4) ι ℂ Xᴴ =
      (Matrix.compRingEquiv (Fin 4) ι ℂ X)ᴴ := rfl

lemma clockMatrix_star_mul (U : Fin 4 → Matrix ι ι ℂ)
    (hU : ∀ t, (U t)ᴴ * U t = 1) : (clockMatrix U)ᴴ * clockMatrix U = 1 := by
  simpa only [map_mul, map_one, clock_flatten_star, clockMatrix] using
    congrArg (Matrix.compRingEquiv (Fin 4) ι ℂ) (weightedClock_star_mul U hU)

lemma clockMatrix_mul_star (U : Fin 4 → Matrix ι ι ℂ)
    (hU : ∀ t, U t * (U t)ᴴ = 1) : clockMatrix U * (clockMatrix U)ᴴ = 1 := by
  simpa only [map_mul, map_one, clock_flatten_star, clockMatrix] using
    congrArg (Matrix.compRingEquiv (Fin 4) ι ℂ) (weightedClock_mul_star U hU)

/-- If all cyclic transition products equal `J`, then the clock satisfies `R⁴=I₄⊗J`. -/
theorem clockMatrix_fourth (U : Fin 4 → Matrix ι ι ℂ) (J : Matrix ι ι ℂ)
    (hcycle : ∀ t, U t * U (t + 1) * U (t + 2) * U (t + 3) = J) :
    clockMatrix U ^ 4 = clockLift J := by
  have hblock : weightedClock U ^ 4 = Matrix.diagonal fun _ : Fin 4 => J := by
    rw [weightedClock_fourth]
    congr 1
    funext t
    exact hcycle t
  simpa only [map_pow, clockMatrix, clockLift] using
    congrArg (Matrix.compRingEquiv (Fin 4) ι ℂ) hblock

end
end CGLMPBounds.Companion
