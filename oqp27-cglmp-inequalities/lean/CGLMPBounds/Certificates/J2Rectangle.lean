module

public import CGLMPBounds.Certificates.J2RectangleData
public import CGLMPBounds.Certificates.J2RectangleColumns
public import CGLMPBounds.Certificates.Bernstein

@[expose] public section


/-!
# Connecting the rectangle certificate to (J.4)

This file connects three independent obligations: rational kernel arithmetic,
Bernstein reconstruction, and a polynomial identity with the source formula.
The generator is never treated as an oracle.
-/

namespace CGLMPBounds.Certificates

noncomputable section

def rectanglePolynomial (θ u : ℝ) : ℝ :=
  ∑ p : Fin 39, ∑ q : Fin 20, (rectangleMonomial p q : ℝ) * θ ^ p.val * u ^ q.val

theorem rectangle_theta_transform_real (i : Fin 39) (q : Fin 20) :
    (rectangleThetaCoefficient i q : ℝ) = ∑ p : Fin 39,
      (rectangleMonomial p q : ℝ) * (i.val.choose p.val : ℝ) /
        ((2 : ℝ) ^ p.val * ((38 : ℕ).choose p.val : ℝ)) := by
  have h := rectangle_theta_transform i q
  unfold certificateChoose at h
  simp only [← Nat.choose_eq_fast_choose] at h
  exact_mod_cast h

theorem rectangle_u_transform_real (i : Fin 39) (j : Fin 20) :
    (rectangleCoefficient i j : ℝ) = ∑ q : Fin 20,
      (rectangleThetaCoefficient i q : ℝ) * (j.val.choose q.val : ℝ) /
        ((19 : ℕ).choose q.val : ℝ) := by
  have h := rectangle_u_transform i j
  unfold certificateChoose at h
  simp only [← Nat.choose_eq_fast_choose] at h
  exact_mod_cast h

theorem rectangle_coefficients_reconstruction (i : Fin 39) (j : Fin 20) :
    (rectangleCoefficient i j : ℝ) = ∑ k : Fin 39 × Fin 20,
      ((rectangleMonomial k.1 k.2 : ℝ) / 2 ^ k.1.val) *
        ((i.val.choose k.1.val : ℝ) / ((38 : ℕ).choose k.1.val : ℝ)) *
        ((j.val.choose k.2.val : ℝ) / ((19 : ℕ).choose k.2.val : ℝ)) := by
  rw [rectangle_u_transform_real]
  simp_rw [rectangle_theta_transform_real, Finset.sum_mul, Finset.sum_div]
  rw [Finset.sum_comm, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  ring

theorem rectangle_bernstein_reconstruction (x y : unitInterval) :
    (∑ i : Fin 39, ∑ j : Fin 20, (rectangleCoefficient i j : ℝ) *
      bernstein 38 i x * bernstein 19 j y) =
        rectanglePolynomial ((x : ℝ) / 2) y := by
  simp_rw [rectangle_coefficients_reconstruction]
  rw [product_bernstein_reconstruction 38 19
    (fun k : Fin 39 × Fin 20 => (rectangleMonomial k.1 k.2 : ℝ) / 2 ^ k.1.val)
    (fun k => k.1.val) (fun k => k.2.val)
    (fun k => by omega) (fun k => by omega)]
  rw [Fintype.sum_prod_type]
  unfold rectanglePolynomial
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  rw [div_pow]
  ring

/-- The generated monomial table is exactly the manuscript's cleared rectangle expression. -/
theorem rectanglePolynomial_eq_source (θ u : ℝ) :
    rectanglePolynomial θ u =
      100 * scalarNumerator θ (scalarY θ u) +
        3 * scalarCoefficientScale * scalarDstar θ :=
  rectangle_monomial_sum_eq_source θ u

/-- The finite polynomial inequality (J.4), including theta=0 and all boundary edges. -/
theorem rectangle_certificate_pos (θ u : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) (1 / 2))
    (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    0 < 100 * scalarNumerator θ (scalarY θ u) +
      3 * scalarCoefficientScale * scalarDstar θ := by
  let x : unitInterval := ⟨2 * θ, by constructor <;> linarith [hθ.1, hθ.2]⟩
  let y : unitInterval := ⟨u, hu⟩
  have hc : ∀ i : Fin 39, ∀ j : Fin 20, (1 : ℝ) ≤ (rectangleCoefficient i j : ℝ) := by
    intro i j
    exact_mod_cast rectangle_coefficients_ge_one i j
  have h := product_bernstein_pos 38 19 (fun i j => (rectangleCoefficient i j : ℝ))
    1 (by norm_num) hc x y
  rw [rectangle_bernstein_reconstruction] at h
  have hx : (x : ℝ) / 2 = θ := by dsimp [x]; ring
  rw [hx, rectanglePolynomial_eq_source] at h
  exact h

end
end CGLMPBounds.Certificates
