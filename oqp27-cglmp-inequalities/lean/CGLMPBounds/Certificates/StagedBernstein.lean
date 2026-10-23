module

public import CGLMPBounds.Certificates.Bernstein
public import Mathlib.Algebra.BigOperators.Field

@[expose] public section


namespace CGLMPBounds.Certificates

/-- Separate the three coefficient components of a product-domain expansion. -/
theorem product_weighted_split {ι κ γ : Type*} [Fintype ι] [Fintype κ] [Fintype γ]
    (r : ι → ℝ) (s : ι → κ → ℝ) (t : ι → γ → ℝ)
    (wi : ι → ℝ) (wj : κ → ℝ) (wg : γ → ℝ)
    (hj : ∑ j, wj j = 1) (hg : ∑ g, wg g = 1) :
    (∑ i, ∑ j, (∑ g, (r i + s i j + t i g) * wg g) * wi i * wj j) =
      (∑ i, r i * wi i) + (∑ i, ∑ j, s i j * wi i * wj j) +
        ∑ i, (∑ g, t i g * wg g) * wi i := by
  have hinner (i : ι) (j : κ) :
      (∑ g, (r i + s i j + t i g) * wg g) = r i + s i j + ∑ g, t i g * wg g := by
    simp only [add_mul, Finset.sum_add_distrib, ← Finset.mul_sum, hg, mul_one]
  simp_rw [hinner, add_mul, Finset.sum_add_distrib]
  simp only [← Finset.mul_sum, hj, mul_one]

/-- The one-variable coefficient transform, with arbitrary interval scaling. -/
theorem interval_bernstein_reconstruction (n : ℕ) (b : ℝ)
    (M C : Fin (n + 1) → ℝ)
    (hC : ∀ i, C i = ∑ p : Fin (n + 1),
      M p * (i.val.choose p.val : ℝ) / (b ^ p.val * (n.choose p.val : ℝ)))
    (x : unitInterval) :
    (∑ i, C i * bernstein n i x) = ∑ p, M p * ((x : ℝ) / b) ^ p.val := by
  simp_rw [hC, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  calc
    _ = (M p / b ^ p.val) *
        ∑ i : Fin (n + 1), ((i.val.choose p.val : ℝ) / (n.choose p.val : ℝ)) *
          bernstein n i x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = M p * ((x : ℝ) / b) ^ p.val := by
      rw [bernstein_monomial n p.val (by omega), div_pow]
      ring

/-- Two separately checked finite coefficient transforms reconstruct a polynomial on a
rescaled rectangle. Splitting the transforms reduces the size of rational kernel checks. -/
theorem staged_bernstein_reconstruction (n m : ℕ) (b : ℝ)
    (M X C : Fin (n + 1) → Fin (m + 1) → ℝ)
    (hX : ∀ i q, X i q = ∑ p : Fin (n + 1),
      M p q * (i.val.choose p.val : ℝ) / (b ^ p.val * (n.choose p.val : ℝ)))
    (hC : ∀ i j, C i j = ∑ q : Fin (m + 1),
      X i q * (j.val.choose q.val : ℝ) / (m.choose q.val : ℝ))
    (x y : unitInterval) :
    (∑ i, ∑ j, C i j * bernstein n i x * bernstein m j y) =
      ∑ p, ∑ q, M p q * ((x : ℝ) / b) ^ p.val * (y : ℝ) ^ q.val := by
  have hcoef (i : Fin (n + 1)) (j : Fin (m + 1)) :
      C i j = ∑ k : Fin (n + 1) × Fin (m + 1),
        (M k.1 k.2 / b ^ k.1.val) *
          ((i.val.choose k.1.val : ℝ) / (n.choose k.1.val : ℝ)) *
          ((j.val.choose k.2.val : ℝ) / (m.choose k.2.val : ℝ)) := by
    rw [hC]
    simp_rw [hX, Finset.sum_mul, Finset.sum_div]
    rw [Finset.sum_comm, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    ring
  simp_rw [hcoef]
  rw [product_bernstein_reconstruction n m
    (fun k : Fin (n + 1) × Fin (m + 1) => M k.1 k.2 / b ^ k.1.val)
    (fun k => k.1.val) (fun k => k.2.val)
    (fun k => by omega) (fun k => by omega)]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  rw [div_pow]
  ring

end CGLMPBounds.Certificates
