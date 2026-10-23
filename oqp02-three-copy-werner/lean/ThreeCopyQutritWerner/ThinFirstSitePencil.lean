module

public import ThreeCopyQutritWerner.ThinFirstSiteOrthogonal

@[expose] public section


/-!
# An actual holomorphic cut-zero pencil from the original thin zero

Normalize arbitrary orthogonal rays only inside the proof. Their literal
unnormalized contractions inherit rank at most two and cut-form zero for
every complex parameter. The middle coefficient itself is not claimed to
have rank at most two.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace ThreeCopyQutritWerner

variable {b c : Type*} [Fintype b] [Fintype c] [DecidableEq b] [DecidableEq c]

/-- The actual contraction is conjugate-linear in its output ray and linear
in its input ray, including zero scalars. -/
theorem firstSiteContraction_smul
    (C : Matrix (Fin 3 × b × c) (Fin 3 × b × c) ℂ)
    (x y : Fin 3 → ℂ) (α β : ℂ) :
    firstSiteContraction C (α • x) (β • y) =
      (conj α * β) • firstSiteContraction C x y := by
  ext r s
  simp only [firstSiteContraction_apply, Pi.smul_apply, Matrix.smul_apply,
    smul_eq_mul, map_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The original zero annihilates all orthogonal ray contractions in the
thin plane, with no normalization or nonzero premise on the rays. -/
theorem firstSiteContraction_cutForm_zero_of_thin_orthogonal
    (C : Matrix (Fin 3 × b × c) (Fin 3 × b × c) ℂ) (hC : C.rank ≤ 2)
    (hz : endpointEnergy C = 0) (hrow : ∀ r q, C (2, r) q = 0)
    (x y : Fin 3 → ℂ) (hxy : braket x y = 0) (hx₂ : x 2 = 0) (hy₂ : y 2 = 0) :
    cutForm (firstSiteContraction C x y) = 0 := by
  by_cases hx : x = 0
  · have he : firstSiteContraction C x y = 0 := by
      ext r s
      simp [firstSiteContraction_apply, hx]
    simp [he, cutForm, frobSq, ptraceL, ptraceR, Matrix.trace]
  by_cases hy : y = 0
  · have he : firstSiteContraction C x y = 0 := by
      ext r s
      simp [firstSiteContraction_apply, hy]
    simp [he, cutForm, frobSq, ptraceL, ptraceR, Matrix.trace]
  have hxn : ∃ i, x i ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact hx (funext hn)
  have hyn : ∃ i, y i ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact hy (funext hn)
  obtain ⟨u, α, hu, hxu⟩ := TwoPlane.exists_unit_factor x hxn
  obtain ⟨v, β, hv, hyv⟩ := TwoPlane.exists_unit_factor y hyn
  have hα : α ≠ 0 := by
    intro he
    exact hx (by ext i; simp [hxu, he])
  have hβ : β ≠ 0 := by
    intro he
    exact hy (by ext i; simp [hyv, he])
  have heX : x = α • u := by ext i; exact hxu i
  have heY : y = β • v := by ext i; exact hyv i
  have hpair : braket x y = (conj α * β) * braket u v := by
    simp only [braket, hxu, hyv, map_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have huv : braket u v = 0 := by
    rw [hpair] at hxy
    have hαc : conj α ≠ 0 := by simpa only [Complex.star_def] using (star_ne_zero.mpr hα)
    exact (mul_eq_zero.mp hxy).resolve_left (mul_ne_zero hαc hβ)
  have hu₂ : u 2 = 0 := (mul_eq_zero.mp ((hxu 2).symm.trans hx₂)).resolve_left hα
  have hv₂ : v 2 = 0 := (mul_eq_zero.mp ((hyv 2).symm.trans hy₂)).resolve_left hβ
  have hq := firstSiteContraction_cutForm_zero_of_thin_orthonormal
    C hC hz hrow u v hu hv huv hu₂ hv₂
  rw [heX, heY, firstSiteContraction_smul, cutForm_smul, hq, mul_zero]

/-- Every complex point of the literal original block pencil is a rank-at-
most-two cut zero. No rank bound is inferred for its middle coefficient. -/
theorem thinFirstSite_quadratic_pencil_rank_cut_zero
    (C : Matrix (Fin 3 × b × c) (Fin 3 × b × c) ℂ) (hC : C.rank ≤ 2)
    (hz : endpointEnergy C = 0) (hrow : ∀ r q, C (2, r) q = 0) (z : ℂ) :
    let T := firstSiteBlock C 0 1 + z • (firstSiteBlock C 1 1 - firstSiteBlock C 0 0) -
      z ^ 2 • firstSiteBlock C 1 0
    T.rank ≤ 2 ∧ cutForm T = 0 := by
  let x : Fin 3 → ℂ := ![1, conj z, 0]
  let y : Fin 3 → ℂ := ![-z, 1, 0]
  have hxy : braket x y = 0 := by simp [x, y, braket, Fin.sum_univ_three]
  have he : firstSiteContraction C x y =
      firstSiteBlock C 0 1 + z • (firstSiteBlock C 1 1 - firstSiteBlock C 0 0) -
        z ^ 2 • firstSiteBlock C 1 0 := by
    ext r s
    simp [firstSiteContraction_apply, x, y, Fin.sum_univ_three,
      firstSiteBlock, Matrix.submatrix_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have hq := firstSiteContraction_cutForm_zero_of_thin_orthogonal C hC hz hrow x y
    hxy (by simp [x]) (by simp [y])
  have hr := (firstSiteContraction_rank_le C x y).trans hC
  rw [he] at hq hr
  exact ⟨hr, hq⟩

end ThreeCopyQutritWerner
