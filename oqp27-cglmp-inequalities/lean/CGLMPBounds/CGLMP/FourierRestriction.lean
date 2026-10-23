module

public import CGLMPBounds.CGLMP.FourierReducingRank
public import CGLMPBounds.Quantum.ProjectionFactor

@[expose] public section


/-!
# Every reducing restriction of the standard amplification is standard

Appendix E.1, p.17. We factor the multiplicity projection obtained from the
actual commutant, then compare two isometries with the same range. Their overlap
is a rectangular unitary, forcing equal dimensions and conjugating all restricted
measurements to the smaller standard amplification.
-/

open Matrix
open scoped Kronecker ComplexOrder
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid
namespace CGLMPBounds
noncomputable section
variable {κ : Type*} [Fintype κ] [DecidableEq κ]
variable (d : ℕ) [NeZero d]

/-- Exact classification of a reducing restriction, in explicit product coordinates.
Both unitary equations are included, so the change of coordinates is surjective. -/
theorem standard_fourier_restriction {n : ℕ}
    (W : Matrix (Fin d × κ) (Fin n) ℂ) (hW : Wᴴ * W = 1)
    (hcomm : ∀ (t : Fin 4) (a : ZMod d),
      (W * Wᴴ) * (fourierProjector d t.val a ⊗ₖ (1 : Matrix κ κ ℂ)) =
        (fourierProjector d t.val a ⊗ₖ (1 : Matrix κ κ ℂ)) * (W * Wᴴ)) :
    ∃ (k : ℕ) (U : Matrix (Fin n) (Fin d × Fin k) ℂ),
      n = d * k ∧ U * Uᴴ = 1 ∧ Uᴴ * U = 1 ∧
      ∀ (t : Fin 4) (a : ZMod d),
        Wᴴ * (fourierProjector d t.val a ⊗ₖ (1 : Matrix κ κ ℂ)) * W =
          U * (fourierProjector d t.val a ⊗ₖ (1 : Matrix (Fin k) (Fin k) ℂ)) * Uᴴ := by
  have hW2 : (W * Wᴴ) * (W * Wᴴ) = W * Wᴴ := by
    calc
      (W * Wᴴ) * (W * Wᴴ) = W * (Wᴴ * W) * Wᴴ := by simp only [Matrix.mul_assoc]
      _ = W * Wᴴ := by rw [hW, Matrix.mul_one]
  obtain ⟨Y, hY, hY2, hXY, _⟩ := reducing_projection_multiplicity d (W * Wᴴ)
    (Matrix.isHermitian_mul_conjTranspose_self W) hW2 hcomm
  obtain ⟨k, B, hB, hB'⟩ := exists_projection_isometry_factor Y hY hY2
  let L : Matrix (Fin d × κ) (Fin d × Fin k) ℂ :=
    (1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ B
  have hL : Lᴴ * L = 1 := by
    dsimp only [L]
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      ← Matrix.mul_kronecker_mul, Matrix.one_mul, hB, Matrix.one_kronecker_one]
  have hL' : L * Lᴴ = W * Wᴴ := by
    dsimp only [L]
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      ← Matrix.mul_kronecker_mul, Matrix.one_mul, hB', hXY]
  let U : Matrix (Fin n) (Fin d × Fin k) ℂ := Wᴴ * L
  have hUU : U * Uᴴ = 1 := by
    dsimp only [U]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc
      (Wᴴ * L) * (Lᴴ * W) = Wᴴ * (L * Lᴴ) * W := by simp only [Matrix.mul_assoc]
      _ = (Wᴴ * W) * (Wᴴ * W) := by rw [hL']; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hW, Matrix.one_mul]
  have hUU' : Uᴴ * U = 1 := by
    dsimp only [U]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc
      (Lᴴ * W) * (Wᴴ * L) = Lᴴ * (W * Wᴴ) * L := by simp only [Matrix.mul_assoc]
      _ = (Lᴴ * L) * (Lᴴ * L) := by rw [← hL']; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hL, Matrix.one_mul]
  have hdim : n = d * k := by
    have ht := Matrix.trace_mul_comm U Uᴴ
    rw [hUU, hUU', Matrix.trace_one, Matrix.trace_one] at ht
    simpa only [Fintype.card_fin, Fintype.card_prod, Nat.cast_inj] using ht
  refine ⟨k, U, hdim, hUU, hUU', ?_⟩
  intro t a
  let A := fourierProjector d t.val a
  have hLA : L * (A ⊗ₖ (1 : Matrix (Fin k) (Fin k) ℂ)) =
      (A ⊗ₖ (1 : Matrix κ κ ℂ)) * L := by
    dsimp only [L]
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
    simp
  change Wᴴ * (A ⊗ₖ (1 : Matrix κ κ ℂ)) * W =
    U * (A ⊗ₖ (1 : Matrix (Fin k) (Fin k) ℂ)) * Uᴴ
  symm
  dsimp only [U]
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  calc
    ((Wᴴ * L) * (A ⊗ₖ (1 : Matrix (Fin k) (Fin k) ℂ))) * (Lᴴ * W) =
      Wᴴ * (L * (A ⊗ₖ (1 : Matrix (Fin k) (Fin k) ℂ))) * Lᴴ * W := by
        simp only [Matrix.mul_assoc]
    _ = Wᴴ * (A ⊗ₖ (1 : Matrix κ κ ℂ)) * (L * Lᴴ) * W := by
      rw [hLA]; simp only [Matrix.mul_assoc]
    _ = Wᴴ * (A ⊗ₖ (1 : Matrix κ κ ℂ)) * W := by
      rw [hL']
      simp only [Matrix.mul_assoc, hW, Matrix.mul_one]

end
end CGLMPBounds
