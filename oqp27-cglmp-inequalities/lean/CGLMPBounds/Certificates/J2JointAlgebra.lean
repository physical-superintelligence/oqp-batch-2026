module

public import CGLMPBounds.Certificates.J2JointData
public import CGLMPBounds.Certificates.StagedBernstein

@[expose] public section


/-!
# Algebraic consequences of the joint-domain rational certificate

The finite data are checked in J2JointData; this module transports the checks to
real arithmetic and proves the common coefficient lower bound for both signs.
Identification with the source polynomial remains a separate obligation.
-/

namespace CGLMPBounds.Certificates

noncomputable section

def jointACleared (θ u : ℝ) : ℝ :=
  ∑ p : Fin 40, ∑ q : Fin 20, (jointAMonomial p q : ℝ) * θ ^ p.val * u ^ q.val

def jointBCleared (θ u : ℝ) : ℝ :=
  ∑ p : Fin 40, ∑ q : Fin 20, (jointBMonomial p q : ℝ) * θ ^ p.val * u ^ q.val

def jointFullCoefficient (σ : ℝ) (i : Fin 40) (j : Fin 20) (g : Fin 210) : ℝ :=
  10^12 * (19568 * (jointDCoefficient i : ℝ) + 810 * (jointTCoefficient i : ℝ)) +
    120000 * (jointACoefficient i j : ℝ) +
    σ * 300000 * ∑ l : Fin 3, (jointBCoefficient i (simplex19Index g l) : ℝ)

theorem joint_A_theta_transform_real (i : Fin 40) (q : Fin 20) :
    (jointAThetaCoefficient i q : ℝ) = ∑ p : Fin 40,
      (jointAMonomial p q : ℝ) * (i.val.choose p.val : ℝ) /
        ((3 : ℝ) ^ p.val * ((39 : ℕ).choose p.val : ℝ)) := by
  have h := joint_A_theta_transform i q
  unfold certificateChoose at h
  simp only [← Nat.choose_eq_fast_choose] at h
  exact_mod_cast h

theorem joint_A_u_transform_real (i : Fin 40) (j : Fin 20) :
    (jointACoefficient i j : ℝ) = ∑ q : Fin 20,
      (jointAThetaCoefficient i q : ℝ) * (j.val.choose q.val : ℝ) /
        ((19 : ℕ).choose q.val : ℝ) := by
  have h := joint_A_u_transform i j
  unfold certificateChoose at h
  simp only [← Nat.choose_eq_fast_choose] at h
  exact_mod_cast h

theorem joint_B_theta_transform_real (i : Fin 40) (q : Fin 20) :
    (jointBThetaCoefficient i q : ℝ) = ∑ p : Fin 40,
      (jointBMonomial p q : ℝ) * (i.val.choose p.val : ℝ) /
        ((3 : ℝ) ^ p.val * ((39 : ℕ).choose p.val : ℝ)) := by
  have h := joint_B_theta_transform i q
  unfold certificateChoose at h
  simp only [← Nat.choose_eq_fast_choose] at h
  exact_mod_cast h

theorem joint_B_u_transform_real (i : Fin 40) (j : Fin 20) :
    (jointBCoefficient i j : ℝ) = ∑ q : Fin 20,
      (jointBThetaCoefficient i q : ℝ) * (j.val.choose q.val : ℝ) /
        ((19 : ℕ).choose q.val : ℝ) := by
  have h := joint_B_u_transform i j
  unfold certificateChoose at h
  simp only [← Nat.choose_eq_fast_choose] at h
  exact_mod_cast h

theorem joint_A_bernstein_reconstruction (x y : unitInterval) :
    (∑ i : Fin 40, ∑ j : Fin 20, (jointACoefficient i j : ℝ) *
      bernstein 39 i x * bernstein 19 j y) = jointACleared ((x : ℝ) / 3) y :=
  staged_bernstein_reconstruction 39 19 3
    (fun p q => (jointAMonomial p q : ℝ))
    (fun i q => (jointAThetaCoefficient i q : ℝ))
    (fun i j => (jointACoefficient i j : ℝ))
    joint_A_theta_transform_real joint_A_u_transform_real x y

theorem joint_B_bernstein_reconstruction (x y : unitInterval) :
    (∑ i : Fin 40, ∑ j : Fin 20, (jointBCoefficient i j : ℝ) *
      bernstein 39 i x * bernstein 19 j y) = jointBCleared ((x : ℝ) / 3) y :=
  staged_bernstein_reconstruction 39 19 3
    (fun p q => (jointBMonomial p q : ℝ))
    (fun i q => (jointBThetaCoefficient i q : ℝ))
    (fun i j => (jointBCoefficient i j : ℝ))
    joint_B_theta_transform_real joint_B_u_transform_real x y

/-- Table J.2 gives a uniform positive lower bound for every full product coefficient,
including both signs in (J.5). The rational checks contain no real-order oracle. -/
theorem joint_full_coefficient_ge_one (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (i : Fin 40) (j : Fin 20) (g : Fin 210) :
    1 ≤ jointFullCoefficient σ i j g := by
  have hA : (jointALower i : ℝ) ≤ (jointACoefficient i j : ℝ) := by
    exact_mod_cast joint_A_lower i j
  have hB : |∑ l : Fin 3, (jointBCoefficient i (simplex19Index g l) : ℝ)| ≤
      (jointBUpper i : ℝ) := by
    exact_mod_cast joint_B_upper i g
  have hD : (1 : ℝ) ≤ (jointDCoefficient i : ℝ) := by
    exact_mod_cast joint_D_ge_one i
  have hmargin : (10^12 : ℝ) *
      (19568 * (jointDCoefficient i : ℝ) + 810 * (jointTCoefficient i : ℝ)) +
        120000 * (jointALower i : ℝ) - 300000 * (jointBUpper i : ℝ) >
          20 * (10^12 : ℝ) * (jointDCoefficient i : ℝ) := by
    exact_mod_cast joint_strict_margins i
  obtain ⟨hBl, hBu⟩ := abs_le.mp hB
  rcases hσ with rfl | rfl <;> unfold jointFullCoefficient <;> nlinarith

/-- The positive joint product expansion. Its equality to the manuscript expression
must be proved before this can be used as (J.5). -/
def jointExpansion (σ : ℝ) (x y : unitInterval) (α : Fin 3 → ℝ) : ℝ :=
  ∑ i : Fin 40, ∑ j : Fin 20,
    (∑ g : Fin 210, jointFullCoefficient σ i j g * simplex19Weight α g) *
      bernstein 39 i x * bernstein 19 j y

theorem jointExpansion_pos (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (x y : unitInterval) (α : Fin 3 → ℝ) (hα : ∀ l, 0 ≤ α l)
    (hsum : ∑ l : Fin 3, α l = 1) : 0 < jointExpansion σ x y α := by
  apply product_bernstein_pos 39 19 _ 1 (by norm_num)
  intro i j
  exact le_simplex19 α hα hsum (jointFullCoefficient σ i j) 1
    (joint_full_coefficient_ge_one σ hσ i j)

end
end CGLMPBounds.Certificates
