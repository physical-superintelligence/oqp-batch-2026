module

public import CGLMPBounds.Certificates.ScalarTruncation
public import CGLMPBounds.Certificates.ScalarFinite
public import CGLMPBounds.Certificates.ScalarDomain
public import CGLMPBounds.Certificates.J2Rectangle
public import CGLMPBounds.Certificates.J2JointSource

@[expose] public section


/-!
# The master scalar inequality and rectangle lower bound of Appendix J

Canonical supplement pp. 37 and 39–40, equations (J.2) and (J.6).
The endpoints use the original independent y and triangle variables. Domain
parametrizations are introduced only inside the proofs, including their
degenerate endpoints at theta=1/2 and theta=1/3.

The coefficient sequence is the source's explicit Bernoulli formula in (I.1).
The finite polynomial certificates, coefficient bounds/enclosures, summability,
and truncation estimate enter through theorem imports, not hypotheses asserting
the desired result.
-/

namespace CGLMPBounds.Certificates

/-- The ten-term replacement of Omega, used only as an intermediate proof object.
Public source endpoints below use `scalarInfiniteTriangle` directly. -/
noncomputable def scalarTenTriangle (θ : ℝ) (x : Fin 3 → ℝ) : ℝ :=
  (1 - 2 * θ) * ∑ j, (scalarTen θ (1 - x j) - scalarTen θ (x j))

/-- Exact identification of the finite triangular combination with its cleared
integer numerator on the parametrized simplex. -/
theorem scalarTenTriangle_eq_numerator {θ : ℝ} (hθ : 0 ≤ θ) (α : Fin 3 → ℝ) :
    scalarTenTriangle θ (scalarX θ α) = scalarTriangleNumerator θ α /
      ((scalarCoefficientScale : ℝ) * scalarDstar θ) := by
  unfold scalarTenTriangle scalarTriangleNumerator
  simp_rw [scalarTen_eq_numerator hθ, ← sub_div]
  rw [← Finset.sum_div]
  ring

/-- The finite rectangle inequality after division by its positive denominator. -/
theorem scalar_finite_rectangle_lower (θ u : ℝ)
    (hθ : θ ∈ Set.Icc (0 : ℝ) (1 / 2)) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    -(3 : ℝ) / 100 < scalarTen θ (scalarY θ u) := by
  have hQ : (0 : ℝ) < scalarCoefficientScale := by norm_num [scalarCoefficientScale]
  have hD := scalarDstar_pos hθ.1
  have hcert := rectangle_certificate_pos θ u hθ hu
  rw [scalarTen_eq_numerator hθ.1]
  apply (lt_div_iff₀ (mul_pos hQ hD)).2
  nlinarith

/-- Dividing (J.5) by 120000 Q D_* gives the exact normalization printed on
p. 39. The rational constant is epsilon_0=9/40000. -/
theorem scalar_finite_joint_positive (θ u σ : ℝ) (α : Fin 3 → ℝ)
    (hθ : θ ∈ Set.Icc (0 : ℝ) (1 / 3)) (hu : u ∈ Set.Icc (0 : ℝ) 1)
    (hα : ∀ j, 0 ≤ α j) (hsum : ∑ j, α j = 1) (hσ : σ = -1 ∨ σ = 1) :
    0 < 1 / 6 - (9 / 40000 : ℝ) * (16 - 30 * θ) +
      scalarTen θ (scalarY θ u) + (σ * (5 / 2)) *
        scalarTenTriangle θ (scalarX θ α) := by
  have hQ : (0 : ℝ) < scalarCoefficientScale := by norm_num [scalarCoefficientScale]
  have hD := scalarDstar_pos hθ.1
  have hden : 0 < (120000 : ℝ) * ((scalarCoefficientScale : ℝ) * scalarDstar θ) :=
    mul_pos (by norm_num) (mul_pos hQ hD)
  have hcert := joint_certificate_pos θ u σ α hθ hu hα hsum hσ
  calc
    0 < ((19568 + 810 * θ) * scalarCoefficientScale * scalarDstar θ +
        120000 * scalarNumerator θ (scalarY θ u) +
        σ * 300000 * scalarTriangleNumerator θ α) /
          (120000 * ((scalarCoefficientScale : ℝ) * scalarDstar θ)) :=
      div_pos hcert hden
    _ = 1 / 6 - (9 / 40000 : ℝ) * (16 - 30 * θ) +
        scalarTen θ (scalarY θ u) + (σ * (5 / 2)) *
          scalarTenTriangle θ (scalarX θ α) := by
      rw [scalarTen_eq_numerator hθ.1, scalarTenTriangle_eq_numerator hθ.1]
      field_simp [hQ.ne', hD.ne']
      <;> ring

/-- The original triangle-domain assumptions put every coordinate in [0,1]. -/
theorem scalar_triangle_coordinate_mem {θ : ℝ} (hθ : 0 ≤ θ)
    (x : Fin 3 → ℝ) (hx : ∀ j, θ ≤ x j) (hsum : ∑ j, x j = 1) (j : Fin 3) :
    x j ∈ Set.Icc (0 : ℝ) 1 := by
  have hx0 : ∀ l, 0 ≤ x l := fun l => hθ.trans (hx l)
  refine ⟨hx0 j, ?_⟩
  rw [← hsum]
  exact Finset.single_le_sum (fun l _ => hx0 l) (Finset.mem_univ j)

/-- There are three triangle coordinates and two errors per coordinate.
The factor 1-2 theta is nonnegative throughout the rectangle domain. -/
theorem scalar_triangle_truncation_error_le {θ : ℝ}
    (hθ : θ ∈ Set.Icc (0 : ℝ) (1 / 2)) (x : Fin 3 → ℝ)
    (hx : ∀ j, x j ∈ Set.Icc (0 : ℝ) 1) :
    |scalarInfiniteTriangle θ x - scalarTenTriangle θ x| ≤
      6 * (1 - 2 * θ) * (9 / 40000 : ℝ) := by
  have hfactor : 0 ≤ 1 - 2 * θ := by linarith [hθ.2]
  have hpoint (j : Fin 3) :
      |(scalarInfinite θ (1 - x j) - scalarInfinite θ (x j)) -
        (scalarTen θ (1 - x j) - scalarTen θ (x j))| ≤
          2 * (9 / 40000 : ℝ) := by
    have hreflect : 1 - x j ∈ Set.Icc (0 : ℝ) 1 := by
      constructor <;> linarith [(hx j).1, (hx j).2]
    have hleft := scalar_truncation_error_lt hθ.1 hreflect
    have hright := scalar_truncation_error_lt hθ.1 (hx j)
    have heq : (scalarInfinite θ (1 - x j) - scalarInfinite θ (x j)) -
        (scalarTen θ (1 - x j) - scalarTen θ (x j)) =
          (scalarInfinite θ (1 - x j) - scalarTen θ (1 - x j)) -
            (scalarInfinite θ (x j) - scalarTen θ (x j)) := by ring
    rw [heq]
    exact (abs_sub _ _).trans (by linarith)
  have hsum : |∑ j : Fin 3,
      ((scalarInfinite θ (1 - x j) - scalarInfinite θ (x j)) -
        (scalarTen θ (1 - x j) - scalarTen θ (x j)))| ≤
          6 * (9 / 40000 : ℝ) := by
    calc
      _ ≤ ∑ j : Fin 3,
          |(scalarInfinite θ (1 - x j) - scalarInfinite θ (x j)) -
            (scalarTen θ (1 - x j) - scalarTen θ (x j))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin 3, 2 * (9 / 40000 : ℝ) :=
        Finset.sum_le_sum (fun j _ => hpoint j)
      _ = 6 * (9 / 40000 : ℝ) := by norm_num
  unfold scalarInfiniteTriangle scalarTenTriangle
  rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_nonneg hfactor]
  calc
    _ ≤ (1 - 2 * θ) * (6 * (9 / 40000 : ℝ)) :=
      mul_le_mul_of_nonneg_left hsum hfactor
    _ = 6 * (1 - 2 * θ) * (9 / 40000 : ℝ) := by ring

/-- The certificates actually give a strict version of (J.2). The theorem below
records the manuscript's non-strict bound with exactly its original domain. -/
theorem scalar_master_strict (θ y : ℝ) (x : Fin 3 → ℝ)
    (hθ : θ ∈ Set.Ioc (0 : ℝ) (1 / 3)) (hy : y ∈ Set.Icc θ (1 - θ))
    (hx : ∀ j, θ ≤ x j) (hsum : ∑ j, x j = 1) :
    (1 / 6 : ℝ) < 1 / 3 + scalarInfinite θ y -
      (5 / 2) * |scalarInfiniteTriangle θ x| := by
  have hθ3 : θ ∈ Set.Icc (0 : ℝ) (1 / 3) := ⟨hθ.1.le, hθ.2⟩
  have hθ2 : θ ∈ Set.Icc (0 : ℝ) (1 / 2) := ⟨hθ.1.le, by linarith [hθ.2]⟩
  have hy01 : y ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> linarith [hy.1, hy.2, hθ.1]
  have hx01 : ∀ j, x j ∈ Set.Icc (0 : ℝ) 1 :=
    scalar_triangle_coordinate_mem hθ.1.le x hx hsum
  obtain ⟨u, hu, huy⟩ := exists_scalarY hθ2 hy
  obtain ⟨α, hα, hαsum, hαx⟩ := exists_scalarX hθ3 x hx hsum
  have hp := scalar_finite_joint_positive θ u 1 α hθ3 hu hα hαsum (Or.inr rfl)
  have hm := scalar_finite_joint_positive θ u (-1) α hθ3 hu hα hαsum (Or.inl rfl)
  rw [huy, hαx] at hp hm
  have hp' : 0 < 1 / 6 - (9 / 40000 : ℝ) * (16 - 30 * θ) +
      scalarTen θ y + (5 / 2) * scalarTenTriangle θ x := by
    simpa only [one_mul] using hp
  have hm' : 0 < 1 / 6 - (9 / 40000 : ℝ) * (16 - 30 * θ) +
      scalarTen θ y - (5 / 2) * scalarTenTriangle θ x := by
    simpa only [neg_mul, one_mul, sub_eq_add_neg] using hm
  exact scalar_master_perturbation θ (9 / 40000) (scalarInfinite θ y) (scalarTen θ y)
    (scalarInfiniteTriangle θ x) (scalarTenTriangle θ x)
    (scalar_truncation_error_lt hθ.1.le hy01).le
    (scalar_triangle_truncation_error_le hθ2 x hx01) hp' hm'

/-- Appendix J, (J.2), with independent y and original triangle coordinates.
No coefficient bound, positivity certificate, or analytic equality is a hypothesis. -/
theorem scalar_master_inequality (θ y : ℝ) (x : Fin 3 → ℝ)
    (hθ : θ ∈ Set.Ioc (0 : ℝ) (1 / 3)) (hy : y ∈ Set.Icc θ (1 - θ))
    (hx : ∀ j, θ ≤ x j) (hsum : ∑ j, x j = 1) :
    (1 / 6 : ℝ) ≤ 1 / 3 + scalarInfinite θ y -
      (5 / 2) * |scalarInfiniteTriangle θ x| :=
  (scalar_master_strict θ y x hθ hy hx hsum).le

/-- Appendix J, (J.6), including theta=0 and the collapsed interval at theta=1/2. -/
theorem scalar_rectangle_lower_bound (θ y : ℝ)
    (hθ : θ ∈ Set.Icc (0 : ℝ) (1 / 2)) (hy : y ∈ Set.Icc θ (1 - θ)) :
    -(3 : ℝ) / 100 - (9 : ℝ) / 40000 < scalarInfinite θ y := by
  have hy01 : y ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> linarith [hy.1, hy.2, hθ.1]
  obtain ⟨u, hu, huy⟩ := exists_scalarY hθ hy
  have hfinite := scalar_finite_rectangle_lower θ u hθ hu
  rw [huy] at hfinite
  have herror := (abs_lt.mp (scalar_truncation_error_lt hθ.1 hy01)).1
  linarith

end CGLMPBounds.Certificates
