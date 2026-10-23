module

public import CGLMPBounds.Certificates.J2JointAlgebra
public import CGLMPBounds.Certificates.J2JointAColumns
public import CGLMPBounds.Certificates.J2JointBColumns

@[expose] public section


/-!
# The joint certificate and the source polynomial

The polynomial identities below are independent of the certificate generator:
separate kernel checks identify each literal table column, then univariate
`ring` identities and a generic affine expansion reconstruct the source formula.
Bernstein marginality then identifies the positive expansion on the full simplex.
This proves only the finite polynomial assertion (J.5); the analytic tail is separate.
-/

namespace CGLMPBounds.Certificates

noncomputable section

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

theorem joint_A_eq_source (θ u : ℝ) :
    jointACleared θ u = scalarNumerator θ (scalarY θ u) :=
  joint_A_monomial_sum_eq_source θ u

theorem joint_B_eq_source (θ u : ℝ) :
    jointBCleared θ u = (1 - 2 * θ) *
      (scalarNumerator θ (1 - (θ + (1 - 3 * θ) * u)) -
        scalarNumerator θ (θ + (1 - 3 * θ) * u)) :=
  joint_B_monomial_sum_eq_source θ u

theorem joint_D_eq_source (θ : ℝ) :
    (∑ p : Fin 40, (jointDMonomial p : ℝ) * θ ^ p.val) = scalarDstar θ := by
  norm_num [jointDMonomial, scalarDstar, Fin.sum_univ_succ, Finset.prod_range_succ]
  ring

theorem joint_T_eq_source (θ : ℝ) :
    (∑ p : Fin 40, (jointTMonomial p : ℝ) * θ ^ p.val) = θ * scalarDstar θ := by
  norm_num [jointTMonomial, scalarDstar, Fin.sum_univ_succ, Finset.prod_range_succ]
  ring

theorem joint_D_transform_real (i : Fin 40) :
    (jointDCoefficient i : ℝ) = ∑ p : Fin 40,
      (jointDMonomial p : ℝ) * (i.val.choose p.val : ℝ) /
        ((3 : ℝ) ^ p.val * ((39 : ℕ).choose p.val : ℝ)) := by
  have h := joint_D_transform i
  unfold certificateChoose at h
  simp only [← Nat.choose_eq_fast_choose] at h
  exact_mod_cast h

theorem joint_T_transform_real (i : Fin 40) :
    (jointTCoefficient i : ℝ) = ∑ p : Fin 40,
      (jointTMonomial p : ℝ) * (i.val.choose p.val : ℝ) /
        ((3 : ℝ) ^ p.val * ((39 : ℕ).choose p.val : ℝ)) := by
  have h := joint_T_transform i
  unfold certificateChoose at h
  simp only [← Nat.choose_eq_fast_choose] at h
  exact_mod_cast h

theorem joint_D_reconstruction (x : unitInterval) :
    (∑ i : Fin 40, (jointDCoefficient i : ℝ) * bernstein 39 i x) =
      scalarDstar ((x : ℝ) / 3) := by
  rw [interval_bernstein_reconstruction 39 3
    (fun p => (jointDMonomial p : ℝ)) (fun i => (jointDCoefficient i : ℝ))
    joint_D_transform_real x, joint_D_eq_source]

theorem joint_T_reconstruction (x : unitInterval) :
    (∑ i : Fin 40, (jointTCoefficient i : ℝ) * bernstein 39 i x) =
      ((x : ℝ) / 3) * scalarDstar ((x : ℝ) / 3) := by
  rw [interval_bernstein_reconstruction 39 3
    (fun p => (jointTMonomial p : ℝ)) (fun i => (jointTCoefficient i : ℝ))
    joint_T_transform_real x, joint_T_eq_source]

theorem joint_B_simplex_reconstruction (x : unitInterval) (α : Fin 3 → ℝ)
    (hα : ∀ l, 0 ≤ α l) (hsum : ∑ l : Fin 3, α l = 1) :
    (∑ i : Fin 40, (∑ g : Fin 210,
      (∑ l : Fin 3, (jointBCoefficient i (simplex19Index g l) : ℝ)) *
        simplex19Weight α g) * bernstein 39 i x) =
      scalarTriangleNumerator ((x : ℝ) / 3) α := by
  calc
    _ = ∑ i : Fin 40, (∑ l : Fin 3, ∑ j : Fin 20,
        (jointBCoefficient i j : ℝ) *
          bernstein 19 j (simplex19Point α hα hsum l)) * bernstein 39 i x := by
      apply Finset.sum_congr rfl
      intro i _
      rw [simplex19_separable_sum α hα hsum (fun j => (jointBCoefficient i j : ℝ))]
    _ = ∑ l : Fin 3, ∑ i : Fin 40, ∑ j : Fin 20,
        (jointBCoefficient i j : ℝ) * bernstein 39 i x *
          bernstein 19 j (simplex19Point α hα hsum l) := by
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ∑ l : Fin 3, jointBCleared ((x : ℝ) / 3) (α l) := by
      apply Finset.sum_congr rfl
      intro l _
      exact joint_B_bernstein_reconstruction x (simplex19Point α hα hsum l)
    _ = scalarTriangleNumerator ((x : ℝ) / 3) α := by
      simp only [joint_B_eq_source, scalarTriangleNumerator, scalarX, Finset.mul_sum]

theorem jointExpansion_eq_source (σ : ℝ) (x y : unitInterval) (α : Fin 3 → ℝ)
    (hα : ∀ l, 0 ≤ α l) (hsum : ∑ l : Fin 3, α l = 1) :
    jointExpansion σ x y α =
      (19568 + 810 * ((x : ℝ) / 3)) * scalarCoefficientScale *
        scalarDstar ((x : ℝ) / 3) +
      120000 * scalarNumerator ((x : ℝ) / 3) (scalarY ((x : ℝ) / 3) y) +
      σ * 300000 * scalarTriangleNumerator ((x : ℝ) / 3) α := by
  unfold jointExpansion jointFullCoefficient
  rw [product_weighted_split
    (fun i : Fin 40 => (10^12 : ℝ) *
      (19568 * (jointDCoefficient i : ℝ) + 810 * (jointTCoefficient i : ℝ)))
    (fun i j => 120000 * (jointACoefficient i j : ℝ))
    (fun i g => σ * 300000 * ∑ l : Fin 3,
      (jointBCoefficient i (simplex19Index g l) : ℝ))
    (fun i => bernstein 39 i x) (fun j => bernstein 19 j y)
    (simplex19Weight α) (bernstein.probability 19 y)
    (simplex19_probability α hα hsum)]
  have hD : (∑ i : Fin 40, (10^12 : ℝ) *
      (19568 * (jointDCoefficient i : ℝ) + 810 * (jointTCoefficient i : ℝ)) *
        bernstein 39 i x) =
      (19568 + 810 * ((x : ℝ) / 3)) * scalarCoefficientScale *
        scalarDstar ((x : ℝ) / 3) := by
    simp only [mul_add, add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
    rw [joint_D_reconstruction, joint_T_reconstruction]
    norm_num [scalarCoefficientScale]
    ring
  have hA : (∑ i : Fin 40, ∑ j : Fin 20,
      120000 * (jointACoefficient i j : ℝ) * bernstein 39 i x * bernstein 19 j y) =
      120000 * scalarNumerator ((x : ℝ) / 3) (scalarY ((x : ℝ) / 3) y) := by
    simp only [mul_assoc, ← Finset.mul_sum]
    have h := joint_A_bernstein_reconstruction x y
    simp only [mul_assoc] at h
    rw [h, joint_A_eq_source]
  have hB : (∑ i : Fin 40, (∑ g : Fin 210,
      (σ * 300000 * ∑ l : Fin 3, (jointBCoefficient i (simplex19Index g l) : ℝ)) *
        simplex19Weight α g) * bernstein 39 i x) =
      σ * 300000 * scalarTriangleNumerator ((x : ℝ) / 3) α := by
    simp only [mul_assoc, ← Finset.mul_sum]
    have h := joint_B_simplex_reconstruction x α hα hsum
    rw [h]
  rw [hD, hA, hB]

/-- Both signs of the source assertion (J.5), with all boundary points included. -/
theorem joint_certificate_pos (θ u σ : ℝ) (α : Fin 3 → ℝ)
    (hθ : θ ∈ Set.Icc (0 : ℝ) (1 / 3)) (hu : u ∈ Set.Icc (0 : ℝ) 1)
    (hα : ∀ j, 0 ≤ α j) (hsum : ∑ j, α j = 1) (hσ : σ = -1 ∨ σ = 1) :
    0 < (19568 + 810 * θ) * scalarCoefficientScale * scalarDstar θ +
      120000 * scalarNumerator θ (scalarY θ u) +
      σ * 300000 * scalarTriangleNumerator θ α := by
  let x : unitInterval := ⟨3 * θ, by constructor <;> linarith [hθ.1, hθ.2]⟩
  let y : unitInterval := ⟨u, hu⟩
  have h := jointExpansion_pos σ hσ.symm x y α hα hsum
  rw [jointExpansion_eq_source σ x y α hα hsum] at h
  have hx : (x : ℝ) / 3 = θ := by dsimp [x]; ring
  rw [hx] at h
  exact h

end
end CGLMPBounds.Certificates
