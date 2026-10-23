module

public import ThreeCopyQutritWerner.ProductRayEnergy
public import ThreeCopyQutritWerner.RankTwo

@[expose] public section


/-!
# Rank-two factorization with a prescribed range vector

The first source column may be chosen to be any specified nonzero range vector.
This is elementary complex row algebra, independent of endpoint positivity.
-/

noncomputable section

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

/-- Choose any nonzero range vector as the first vector of a rank-two decomposition.
The second covector is necessarily nonzero; no orthogonality is imposed. -/
theorem rank_two_factor_with_prescribed_range {m n : Type*} [Fintype m] [Fintype n]
    (C : Matrix m n ℂ) (p : m → ℂ) (hp : p ≠ 0) (hr : C.rank = 2)
    (hrange : ∃ z, C *ᵥ z = p) :
    ∃ (b : n → ℂ) (x : m → ℂ) (d : n → ℂ), d ≠ 0 ∧
      ∀ i j, C i j = p i * b j + x i * d j := by
  classical
  obtain ⟨X, B, hC⟩ := (rank_le_iff_exists_mul C 2).mp hr.le
  obtain ⟨z, hz⟩ := hrange
  let t := B *ᵥ z
  have ht : X *ᵥ t = p := by
    change X *ᵥ (B *ᵥ z) = p
    rw [Matrix.mulVec_mulVec, ← hC]
    exact hz
  have hti : ∀ i, X i 0 * t 0 + X i 1 * t 1 = p i := by
    intro i
    have h := congrFun ht i
    simpa only [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h
  have hCi : ∀ i j, C i j = X i 0 * B 0 j + X i 1 * B 1 j := by
    intro i j
    rw [hC, Matrix.mul_apply, Fin.sum_univ_two]
  have finish : ∀ (b : n → ℂ) (x : m → ℂ) (d : n → ℂ),
      (∀ i j, C i j = p i * b j + x i * d j) → d ≠ 0 := by
    intro b x d hf hd
    have he : C = Matrix.vecMulVec p b := by
      ext i j
      simpa only [hf, hd, Pi.zero_apply, mul_zero, add_zero, Matrix.vecMulVec_apply]
    have hle := Matrix.rank_vecMulVec_le p b
    rw [← he, hr] at hle
    omega
  by_cases ht0 : t 0 = 0
  · have ht1 : t 1 ≠ 0 := by
      intro ht1
      apply hp
      funext i
      have hi := hti i
      simpa only [ht0, ht1, mul_zero, add_zero, Pi.zero_apply] using hi.symm
    let b : n → ℂ := fun j => B 1 j / t 1
    let x : m → ℂ := fun i => X i 0
    let d : n → ℂ := fun j => B 0 j
    have hf : ∀ i j, C i j = p i * b j + x i * d j := by
      intro i j
      rw [hCi, ← hti]
      simp only [b, x, d, ht0, mul_zero, zero_add]
      field_simp [ht1]
      ring
    exact ⟨b, x, d, finish b x d hf, hf⟩
  · let b : n → ℂ := fun j => B 0 j / t 0
    let x : m → ℂ := fun i => X i 1
    let d : n → ℂ := fun j => B 1 j - t 1 * B 0 j / t 0
    have hf : ∀ i j, C i j = p i * b j + x i * d j := by
      intro i j
      rw [hCi, ← hti]
      simp only [b, x, d]
      field_simp [ht0]
      ring
    exact ⟨b, x, d, finish b x d hf, hf⟩

/-- The canonical-ray energy ansatz covers every rank-two matrix containing that ray. -/
theorem exists_productRayMatrix_of_canonical_in_range
    (C : Matrix ProductRayShore ProductRayShore ℂ) (hr : C.rank = 2)
    (hrange : ∃ z, C *ᵥ z = fun i => if i = (0, 0, 0) then 1 else 0) :
    ∃ b x d, d ≠ 0 ∧ C = productRayMatrix b x d := by
  obtain ⟨b, x, d, hd, hf⟩ := rank_two_factor_with_prescribed_range C
    (fun i => if i = (0, 0, 0) then 1 else 0)
    (by intro h; have he := congrFun h (0, 0, 0); norm_num at he) hr hrange
  refine ⟨b, x, d, hd, ?_⟩
  ext i j
  rw [hf]
  by_cases hi : i = (0, 0, 0) <;> simp [productRayMatrix, hi]

end ThreeCopyQutritWerner
