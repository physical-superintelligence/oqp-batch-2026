module

public import ThreeCopyQutritWerner.ProductRayLocal
public import ThreeCopyQutritWerner.ZeroRelationsLocalSpan

@[expose] public section


/-!
# Local support forced by the product-ray comparison defects

These are the equality consequences of the local Gram factor. The analytic
step forcing those defects to vanish at an energy zero is a separate obligation.
-/

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

/-- If the product-ray defects vanish against a nonzero second vector, the first
vector has local support in the vacuum plus a single additional direction. -/
theorem productRay_defects_force_local_plane {R S : Type*}
    (x : Fin 3 → R → ℂ) (y : Fin 3 → S → ℂ)
    (hy : ∃ j s, y j s ≠ 0)
    (h10 : ∀ r s, x 1 r * y 0 s = 0)
    (h20 : ∀ r s, x 2 r * y 0 s = 0)
    (h12 : ∀ r s, x 1 r * y 2 s = x 2 r * y 1 s) :
    ∃ (u : Fin 3 → ℂ) (v : R → ℂ),
      ∀ i r, x i r = (if i = 0 then 1 else 0) * x 0 r + u i * v r := by
  obtain ⟨j, s, hy⟩ := hy
  fin_cases j
  · refine ⟨0, 0, ?_⟩
    intro i r
    have hz1 := (mul_eq_zero.mp (h10 r s)).resolve_right hy
    have hz2 := (mul_eq_zero.mp (h20 r s)).resolve_right hy
    fin_cases i <;> simp [hz1, hz2]
  · refine ⟨![0, 1, y 2 s / y 1 s], fun r => x 1 r, ?_⟩
    intro i r
    fin_cases i
    · simp
    · simp
    · change x 2 r = 0 * x 0 r + (y 2 s / y 1 s) * x 1 r
      simp only [zero_mul, zero_add]
      calc
        x 2 r = (x 1 r * y 2 s) / y 1 s := (eq_div_iff hy).2 (h12 r s).symm
        _ = (y 2 s / y 1 s) * x 1 r := by ring
  · refine ⟨![0, y 1 s / y 2 s, 1], fun r => x 2 r, ?_⟩
    intro i r
    fin_cases i
    · simp
    · change x 1 r = 0 * x 0 r + (y 1 s / y 2 s) * x 2 r
      simp only [zero_mul, zero_add]
      calc
        x 1 r = (x 2 r * y 1 s) / y 2 s := (eq_div_iff hy).2 (h12 r s)
        _ = (y 1 s / y 2 s) * x 2 r := by ring
    · simp

/-- An explicit rank-two source containing the canonical product ray is thin at
site 1 whenever the local comparison defects vanish. Corange factors need not be
orthogonal, equal to the source factors, or normalized. -/
theorem localRangeDim₁_le_two_of_productRay_defects
    {b c : Type*} [Fintype b] [Fintype c]
    (C : Matrix (Fin 3 × b × c) (Fin 3 × b × c) ℂ)
    (x : Fin 3 → b × c → ℂ) (y : Fin 3 → b × c → ℂ)
    (b₀ : Matrix (b × c) (Fin 3 × b × c) ℂ) (d : Fin 3 × b × c → ℂ)
    (hy : ∃ j s, y j s ≠ 0)
    (h10 : ∀ r s, x 1 r * y 0 s = 0)
    (h20 : ∀ r s, x 2 r * y 0 s = 0)
    (h12 : ∀ r s, x 1 r * y 2 s = x 2 r * y 1 s)
    (hC : ∀ i r s, C (i, r) s = (if i = 0 then 1 else 0) * b₀ r s + x i r * d s) :
    localRangeDim₁ C ≤ 2 := by
  obtain ⟨u, v, hx⟩ := productRay_defects_force_local_plane x y hy h10 h20 h12
  apply localRangeDim₁_le_two_of_range_plane C (fun i => if i = 0 then 1 else 0) u
    (fun r s => b₀ r s + x 0 r * d s) (fun r s => v r * d s)
  intro i r s
  rw [hC, hx]
  ring

end ThreeCopyQutritWerner
