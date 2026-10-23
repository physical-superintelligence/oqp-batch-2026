module

public import ThreeCopyQutritWerner.CertificateReduction

@[expose] public section


/-!
# Exact polarization and completion of a Hermitian quadratic form

All identities are complex identities before taking real parts.  The completion
requires explicit compression and inverse identities; it assumes no endpoint
inequality or positivity of the residual.
-/

noncomputable section

open scoped BigOperators Matrix ComplexOrder

namespace ThreeCopyQutritWerner

/-- Sesquilinear form associated with a matrix, with the same convention as `expectation`. -/
def productRayPairing {n : Type*} [Fintype n] (M : Matrix n n ℂ) (u v : n → ℂ) : ℂ :=
  star u ⬝ᵥ (M *ᵥ v)

theorem productRayPairing_self {n : Type*} [Fintype n]
    (M : Matrix n n ℂ) (u : n → ℂ) : productRayPairing M u u = expectation M u :=
  (expectation_eq_dotProduct M u).symm

theorem productRayPairing_add_left {n : Type*} [Fintype n]
    (M : Matrix n n ℂ) (u v w : n → ℂ) :
    productRayPairing M (u + v) w = productRayPairing M u w + productRayPairing M v w := by
  simp [productRayPairing, star_add, add_dotProduct]

theorem productRayPairing_add_right {n : Type*} [Fintype n]
    (M : Matrix n n ℂ) (u v w : n → ℂ) :
    productRayPairing M u (v + w) = productRayPairing M u v + productRayPairing M u w := by
  simp [productRayPairing, Matrix.mulVec_add, dotProduct_add]

theorem productRayPairing_star {n : Type*} [Fintype n]
    (M : Matrix n n ℂ) (hM : Mᴴ = M) (u v : n → ℂ) :
    star (productRayPairing M u v) = productRayPairing M v u := by
  have hentry : ∀ i j, star (M i j) = M j i := fun i j =>
    congrFun (congrFun hM j) i
  simp only [productRayPairing, Matrix.mulVec, dotProduct, Pi.star_apply,
    Finset.mul_sum, star_sum, star_mul', star_star, hentry]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Exact vector polarization; the two cross terms have their actual complex phases. -/
theorem productRay_expectation_add_vec {n : Type*} [Fintype n]
    (M : Matrix n n ℂ) (u v : n → ℂ) :
    expectation M (u + v) = expectation M u + expectation M v +
      productRayPairing M u v + productRayPairing M v u := by
  rw [← productRayPairing_self, productRayPairing_add_left,
    productRayPairing_add_right, productRayPairing_add_right,
    productRayPairing_self, productRayPairing_self]
  ring

/-- Moving an embedding across the first slot uses its Hermitian adjoint. -/
theorem productRayPairing_mulVec_left {n m : Type*} [Fintype n] [Fintype m]
    (T : Matrix n n ℂ) (E : Matrix n m ℂ) (b : m → ℂ) (z : n → ℂ) :
    productRayPairing T (E *ᵥ b) z = star b ⬝ᵥ ((Eᴴ * T) *ᵥ z) := by
  rw [productRayPairing, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec]

/-- Completing the square on a specified embedded subspace. `R` is the explicitly
verified inverse of its quadratic coefficient `D`. No positivity premise is used. -/
theorem productRay_complete_square {n m : Type*} [Fintype n] [Fintype m]
    [DecidableEq m]
    (T : Matrix n n ℂ) (E : Matrix n m ℂ) (D R : Matrix m m ℂ)
    (hT : Tᴴ = T) (hD : Dᴴ = D) (hR : Rᴴ = R)
    (hcompress : Eᴴ * T * E = D) (hDR : D * R = 1)
    (b : m → ℂ) (z : n → ℂ) :
    expectation T (E *ᵥ b + z) =
      expectation D (b + R *ᵥ ((Eᴴ * T) *ᵥ z)) + expectation T z -
        expectation ((Eᴴ * T)ᴴ * R * (Eᴴ * T)) z := by
  let L := Eᴴ * T
  let u := L *ᵥ z
  let s := R *ᵥ u
  have hfirst : expectation T (E *ᵥ b) = expectation D b := by
    rw [expectation_mulVec_conj, hcompress]
  have hcross : productRayPairing T (E *ᵥ b) z = productRayPairing D b s := by
    rw [productRayPairing_mulVec_left]
    change star b ⬝ᵥ u = star b ⬝ᵥ (D *ᵥ (R *ᵥ u))
    rw [Matrix.mulVec_mulVec, hDR, Matrix.one_mulVec]
  have hreverse : productRayPairing T z (E *ᵥ b) = productRayPairing D s b := by
    rw [← productRayPairing_star T hT, ← productRayPairing_star D hD, hcross]
  have hshift : expectation D s = expectation (Lᴴ * R * L) z := by
    change expectation D (R *ᵥ (L *ᵥ z)) = _
    rw [expectation_mulVec_conj, hR]
    have hRDR : R * D * R = R := by
      rw [Matrix.mul_assoc, hDR, Matrix.mul_one]
    rw [hRDR, expectation_mulVec_conj]
  change expectation T (E *ᵥ b + z) = expectation D (b + s) +
    expectation T z - expectation (Lᴴ * R * L) z
  rw [productRay_expectation_add_vec, productRay_expectation_add_vec,
    hfirst, hcross, hreverse, hshift]
  ring

/-- Expectation is invariant under an exact relabeling of all basis coordinates. -/
theorem productRay_expectation_submatrix_equiv {n m : Type*} [Fintype n] [Fintype m]
    (e : n ≃ m) (M : Matrix m m ℂ) (v : n → ℂ) :
    expectation (M.submatrix e e) v = expectation M (v ∘ e.symm) := by
  unfold expectation
  refine Fintype.sum_equiv e _ _ ?_
  intro i
  refine Fintype.sum_equiv e _ _ ?_
  intro j
  simp [Function.comp_def]

end ThreeCopyQutritWerner
