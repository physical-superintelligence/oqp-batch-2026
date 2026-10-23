module

public import CGLMPBounds.Companion.FourierBlocks

@[expose] public section


/-!
# Normalizing the frequency blocks to fourth-root unitaries

This is the finite representation step: a unitary whose fourth power is `J ⊗ I`
has the source Fourier representation with blocks `λ_j V_j`, where every `V_j`
is unitary and has fourth power one. No companion tuple is assumed in the input.
-/

open Matrix
open scoped Kronecker
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

namespace CGLMPBounds.Companion
noncomputable section

variable {d : ℕ} [NeZero d]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma frequencyBlock_star_mul (W : Matrix (Fin d × ι) (Fin d × ι) ℂ)
    (hfour : W ^ 4 = Matrix.diagonal (fun p : Fin d × ι => outcomeRoot p.1))
    (hunitary : Wᴴ * W = 1) (j : Fin d) :
    (frequencyBlock W j)ᴴ * frequencyBlock W j = 1 := by
  have he : frequencyDiagonal (fun j => (frequencyBlock W j)ᴴ * frequencyBlock W j) =
      frequencyDiagonal (1 : Fin d → Matrix ι ι ℂ) := by
    calc
      _ = frequencyDiagonal (fun j => (frequencyBlock W j)ᴴ) *
          frequencyDiagonal (frequencyBlock W) :=
        map_mul frequencyDiagonal _ _
      _ = Wᴴ * W := by rw [frequencyDiagonal_star, ← frequency_eq_diagonal W hfour]
      _ = _ := by rw [hunitary, map_one]
  exact congrFun (frequencyDiagonal_injective he) j

lemma frequencyBlock_mul_star (W : Matrix (Fin d × ι) (Fin d × ι) ℂ)
    (hfour : W ^ 4 = Matrix.diagonal (fun p : Fin d × ι => outcomeRoot p.1))
    (hunitary : W * Wᴴ = 1) (j : Fin d) :
    frequencyBlock W j * (frequencyBlock W j)ᴴ = 1 := by
  have he : frequencyDiagonal (fun j => frequencyBlock W j * (frequencyBlock W j)ᴴ) =
      frequencyDiagonal (1 : Fin d → Matrix ι ι ℂ) := by
    calc
      _ = frequencyDiagonal (frequencyBlock W) *
          frequencyDiagonal (fun j => (frequencyBlock W j)ᴴ) :=
        map_mul frequencyDiagonal _ _
      _ = W * Wᴴ := by rw [frequencyDiagonal_star, ← frequency_eq_diagonal W hfour]
      _ = _ := by rw [hunitary, map_one]
  exact congrFun (frequencyDiagonal_injective he) j

lemma frequencyBlock_fourth (W : Matrix (Fin d × ι) (Fin d × ι) ℂ)
    (hfour : W ^ 4 = Matrix.diagonal (fun p : Fin d × ι => outcomeRoot p.1)) (j : Fin d) :
    frequencyBlock W j ^ 4 = outcomeRoot j • (1 : Matrix ι ι ℂ) := by
  have he : frequencyDiagonal (fun j => frequencyBlock W j ^ 4) =
      frequencyDiagonal (fun j => outcomeRoot j • (1 : Matrix ι ι ℂ)) := by
    calc
      _ = frequencyDiagonal (frequencyBlock W) ^ 4 := map_pow frequencyDiagonal _ 4
      _ = W ^ 4 := by rw [← frequency_eq_diagonal W hfour]
      _ = _ := hfour.trans frequencyDiagonal_roots.symm
  exact congrFun (frequencyDiagonal_injective he) j

/-- Divide the frequency block by the source phase; conjugation is its inverse. -/
def normalizedFrequencyBlock (W : Matrix (Fin d × ι) (Fin d × ι) ℂ) (j : Fin d) :
    Matrix ι ι ℂ :=
  star (sourcePhase j) • frequencyBlock W j

lemma normalizedFrequencyBlock_recover (W : Matrix (Fin d × ι) (Fin d × ι) ℂ)
    (j : Fin d) : sourcePhase j • normalizedFrequencyBlock W j = frequencyBlock W j := by
  rw [normalizedFrequencyBlock, smul_smul, mul_comm (sourcePhase j),
    sourcePhase_star_mul, one_smul]

lemma normalizedFrequencyBlock_star_mul (W : Matrix (Fin d × ι) (Fin d × ι) ℂ)
    (hfour : W ^ 4 = Matrix.diagonal (fun p : Fin d × ι => outcomeRoot p.1))
    (hunitary : Wᴴ * W = 1) (j : Fin d) :
    (normalizedFrequencyBlock W j)ᴴ * normalizedFrequencyBlock W j = 1 := by
  rw [normalizedFrequencyBlock, Matrix.conjTranspose_smul, star_star,
    smul_mul_smul_comm, frequencyBlock_star_mul W hfour hunitary,
    mul_comm (sourcePhase j), sourcePhase_star_mul, one_smul]

lemma normalizedFrequencyBlock_mul_star (W : Matrix (Fin d × ι) (Fin d × ι) ℂ)
    (hfour : W ^ 4 = Matrix.diagonal (fun p : Fin d × ι => outcomeRoot p.1))
    (hunitary : W * Wᴴ = 1) (j : Fin d) :
    normalizedFrequencyBlock W j * (normalizedFrequencyBlock W j)ᴴ = 1 := by
  rw [normalizedFrequencyBlock, Matrix.conjTranspose_smul, star_star,
    smul_mul_smul_comm, frequencyBlock_mul_star W hfour hunitary,
    sourcePhase_star_mul, one_smul]

lemma normalizedFrequencyBlock_fourth (W : Matrix (Fin d × ι) (Fin d × ι) ℂ)
    (hfour : W ^ 4 = Matrix.diagonal (fun p : Fin d × ι => outcomeRoot p.1)) (j : Fin d) :
    normalizedFrequencyBlock W j ^ 4 = 1 := by
  rw [normalizedFrequencyBlock, smul_pow, frequencyBlock_fourth W hfour,
    ← sourcePhase_fourth, smul_smul, ← mul_pow, sourcePhase_star_mul, one_pow, one_smul]

/-- Fourier representation with actual fourth-root unitary blocks, from the original operator. -/
theorem fourthRoot_frequency_representation
    (X : Matrix (ZMod d × ι) (ZMod d × ι) ℂ)
    (hleft : Xᴴ * X = 1) (hright : X * Xᴴ = 1)
    (hfour : X ^ 4 = outcomeShift ⊗ₖ (1 : Matrix ι ι ℂ)) :
    ∃ V : Fin d → Matrix.unitaryGroup ι ℂ,
      (∀ j, (V j : Matrix ι ι ℂ) ^ 4 = 1) ∧
      X = liftedFourier (d := d) (ι := ι) *
        frequencyDiagonal (fun j => sourcePhase j • (V j : Matrix ι ι ℂ)) *
          (liftedFourier (d := d) (ι := ι))ᴴ := by
  let W := frequencyConjugate X
  have hWfour : W ^ 4 = Matrix.diagonal (fun p : Fin d × ι => outcomeRoot p.1) := by
    dsimp only [W]
    rw [← frequencyConjugate_pow, hfour, frequencyConjugate_shift]
  have hWleft : Wᴴ * W = 1 := by
    dsimp only [W]
    rw [← frequencyConjugate_star, frequencyConjugate_mul, hleft, frequencyConjugate_one]
  have hWright : W * Wᴴ = 1 := by
    dsimp only [W]
    rw [← frequencyConjugate_star, frequencyConjugate_mul, hright, frequencyConjugate_one]
  let V : Fin d → Matrix.unitaryGroup ι ℂ := fun j =>
    ⟨normalizedFrequencyBlock W j,
      normalizedFrequencyBlock_star_mul W hWfour hWleft j,
      normalizedFrequencyBlock_mul_star W hWfour hWright j⟩
  refine ⟨V, ?_, ?_⟩
  · intro j
    exact normalizedFrequencyBlock_fourth W hWfour j
  · have hblocks : (fun j => sourcePhase j • (V j : Matrix ι ι ℂ)) =
        frequencyBlock W := by
      funext j
      exact normalizedFrequencyBlock_recover W j
    rw [hblocks, ← frequency_eq_diagonal W hWfour]
    exact (frequencyConjugate_reconstruct X).symm

end
end CGLMPBounds.Companion
