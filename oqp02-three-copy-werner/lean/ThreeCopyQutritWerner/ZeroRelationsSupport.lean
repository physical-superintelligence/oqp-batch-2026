module

public import ThreeCopyQutritWerner.ZeroRelationsAlgebra
public import ThreeCopyQutritWerner.AppendixCInputs

@[expose] public section


/-!
# Source-bivector support algebra

The coordinate form of `Aᵢp=0` forces a common one-dimensional local factor of the two
independent source columns. This is the first support step of Appendix C. The general
minor argument below is independent of endpoint positivity and the certificate.
-/

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

/-- The alternating form on two source coefficients. -/
def sourceDet (v w : Fin 2 → ℂ) : ℂ := v 0 * w 1 - v 1 * w 0

/-- Two independent rows detect equality of source coefficient vectors. -/
theorem eq_of_sourceDet_eq (a b v w : Fin 2 → ℂ) (hd : sourceDet a b ≠ 0)
    (h1 : sourceDet v a = sourceDet w a) (h2 : sourceDet v b = sourceDet w b) : v = w := by
  funext k
  have hz : sourceDet a b * (v k - w k) = 0 := by
    simp only [sourceDet] at h1 h2
    fin_cases k
    · change (a 0 * b 1 - a 1 * b 0) * (v 0 - w 0) = 0
      linear_combination a 0 * h2 - b 0 * h1
    · change (a 0 * b 1 - a 1 * b 0) * (v 1 - w 1) = 0
      linear_combination a 1 * h2 - b 1 * h1
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hd)

/-- In a two-vector basis, a zero determinant means scalar proportionality. -/
theorem eq_smul_of_sourceDet_eq_zero (a b v : Fin 2 → ℂ) (hd : sourceDet a b ≠ 0)
    (hv : sourceDet v a = 0) :
    v = fun k => (sourceDet v b / sourceDet a b) * a k := by
  apply eq_of_sourceDet_eq a b _ _ hd
  · rw [hv]
    simp only [sourceDet]
    ring
  · have hc : (sourceDet v b / sourceDet a b) * sourceDet a b = sourceDet v b :=
      div_mul_cancel₀ _ hd
    calc
      sourceDet v b = (sourceDet v b / sourceDet a b) * sourceDet a b := hc.symm
      _ = _ := by simp only [sourceDet]; ring

/-- A rank-two source matrix has two rows with a nonzero determinant. -/
theorem exists_sourceDet_ne_zero_of_rank_two {n : Type*} [Fintype n]
    (X : Matrix n (Fin 2) ℂ) (hr : X.rank = 2) :
    ∃ i j, sourceDet (X i) (X j) ≠ 0 := by
  classical
  by_contra hn
  push_neg at hn
  have hr1 : X.rank ≤ 1 := by
    by_cases hx : ∀ i, X i 0 = 0
    · apply (rank_le_iff_exists_mul X 1).mpr
      refine ⟨Matrix.of fun i _ => X i 1,
        Matrix.of fun (_ : Fin 1) j => if j = 0 then 0 else 1, ?_⟩
      ext i j
      fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_one, hx]
    · push_neg at hx
      obtain ⟨i₀, hi₀⟩ := hx
      apply (rank_le_iff_exists_mul X 1).mpr
      refine ⟨Matrix.of fun i _ => X i 0,
        Matrix.of fun (_ : Fin 1) j => if j = 0 then 1 else X i₀ 1 / X i₀ 0, ?_⟩
      ext i j
      fin_cases j
      · simp [Matrix.mul_apply, Fin.sum_univ_one]
      · simp only [Matrix.mul_apply, Fin.sum_univ_one, Matrix.of_apply]
        change X i 1 = X i 0 * (X i₀ 1 / X i₀ 0)
        rw [mul_div_assoc', eq_div_iff hi₀]
        have he := hn i i₀
        simp only [sourceDet] at he
        linear_combination -he
  omega

/-- The four-row Plücker identity, directly in the two source coordinates. -/
theorem sourceDet_plucker (a b c d : Fin 2 → ℂ) :
    sourceDet a b * sourceDet c d - sourceDet a c * sourceDet b d +
      sourceDet a d * sourceDet b c = 0 := by
  simp only [sourceDet]
  ring

/-- The local symmetry of the bivector forces zero determinant for rows with equal
complementary coordinates. -/
theorem sourceDet_same_right_eq_zero {L R : Type*} (X : Matrix (L × R) (Fin 2) ℂ)
    (h : ∀ i j r s, sourceDet (X (i, r)) (X (j, s)) =
      sourceDet (X (j, r)) (X (i, s))) (i j : L) (r : R) :
    sourceDet (X (i, r)) (X (j, r)) = 0 := by
  have he := h i j r r
  simp only [sourceDet] at he ⊢
  linear_combination he / 2

/-- Local bivector symmetry moves a nonzero determinant to two rows sharing the local
index. This is the decomposability step; arbitrary bivectors would not satisfy it. -/
theorem exists_same_left_sourceDet_ne_zero {L R : Type*}
    (X : Matrix (L × R) (Fin 2) ℂ)
    (h : ∀ i j r s, sourceDet (X (i, r)) (X (j, s)) =
      sourceDet (X (j, r)) (X (i, s)))
    (hn : ∃ p q, sourceDet (X p) (X q) ≠ 0) :
    ∃ i r s, sourceDet (X (i, r)) (X (i, s)) ≠ 0 := by
  obtain ⟨⟨i, r⟩, ⟨j, s⟩, hij⟩ := hn
  refine ⟨i, r, s, ?_⟩
  have hp := sourceDet_plucker (X (i, r)) (X (i, s)) (X (j, r)) (X (j, s))
  have hbc : sourceDet (X (i, s)) (X (j, r)) = -sourceDet (X (i, r)) (X (j, s)) := by
    rw [h i j r s]
    simp only [sourceDet]
    ring
  rw [sourceDet_same_right_eq_zero X h i j r,
    sourceDet_same_right_eq_zero X h i j s, hbc] at hp
  intro hz
  rw [hz] at hp
  have hsq : sourceDet (X (i, r)) (X (j, s)) * sourceDet (X (i, r)) (X (j, s)) = 0 := by
    linear_combination -hp
  exact mul_ne_zero hij hij hsq

/-- Two independent source columns with locally symmetric bivector have a common
one-dimensional local factor. -/
theorem exists_source_factor_of_bivector_symmetry {L R : Type*} [Fintype L] [Fintype R]
    (X : Matrix (L × R) (Fin 2) ℂ) (hr : X.rank = 2)
    (h : ∀ i j r s, sourceDet (X (i, r)) (X (j, s)) =
      sourceDet (X (j, r)) (X (i, s))) :
    ∃ (u : L → ℂ) (Y : Matrix R (Fin 2) ℂ), ∀ i r k, X (i, r) k = u i * Y r k := by
  obtain ⟨i₀, r₀, r₁, hd⟩ := exists_same_left_sourceDet_ne_zero X h
    (exists_sourceDet_ne_zero_of_rank_two X hr)
  let u : L → ℂ := fun i => sourceDet (X (i, r₀)) (X (i₀, r₁)) /
    sourceDet (X (i₀, r₀)) (X (i₀, r₁))
  have h0 : ∀ i, X (i, r₀) = fun k => u i * X (i₀, r₀) k := by
    intro i
    exact eq_smul_of_sourceDet_eq_zero _ _ _ hd (sourceDet_same_right_eq_zero X h i i₀ r₀)
  have h1 : ∀ i, X (i, r₁) = fun k => u i * X (i₀, r₁) k := by
    intro i
    apply eq_of_sourceDet_eq (X (i₀, r₀)) (X (i₀, r₁)) _ _ hd
    · rw [h i i₀ r₁ r₀, h0 i]
      simp only [sourceDet]
      ring
    · rw [sourceDet_same_right_eq_zero X h i i₀ r₁]
      simp only [sourceDet]
      ring
  refine ⟨u, fun r => X (i₀, r), ?_⟩
  intro i r k
  apply congrFun (eq_of_sourceDet_eq (X (i₀, r₀)) (X (i₀, r₁)) (X (i, r))
    (fun j => u i * X (i₀, r) j) hd ?_ ?_) k
  · rw [h i i₀ r r₀, h0 i]
    simp only [sourceDet]
    ring
  · rw [h i i₀ r r₁, h1 i]
    simp only [sourceDet]
    ring

section LocalAntisymmetry

variable {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]

private theorem inv_sqrt_two_complex_ne_zero : ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ≠ 0 := by
  exact_mod_cast inv_ne_zero (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2))

/-- Appendix C, site 1: `A₁p=0` forces a common one-dimensional first-site source factor. -/
theorem exists_source_factor₁_of_siteAnti₁_bivec_eq_zero
    (X : Matrix (a × b × c) (Fin 2) ℂ) (hr : X.rank = 2)
    (hp : siteAnti₁ (bivecMat X) = 0) :
    ∃ (u : a → ℂ) (Y : Matrix (b × c) (Fin 2) ℂ),
      ∀ r k, X r k = u r.1 * Y r.2 k := by
  have hsym : ∀ i j (r s : b × c), sourceDet (X (i, r)) (X (j, s)) =
      sourceDet (X (j, r)) (X (i, s)) := by
    intro i j r s
    have he := congrFun (congrFun hp (i, r)) (j, s)
    simp only [siteAnti₁, Matrix.of_apply, siteSwap₁, Equiv.coe_fn_mk, bivecMat_apply,
      Matrix.zero_apply] at he
    have hz : (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) *
        (sourceDet (X (i, r)) (X (j, s)) - sourceDet (X (j, r)) (X (i, s))) = 0 := by
      simp only [sourceDet]
      linear_combination 2 * he
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left inv_sqrt_two_complex_ne_zero)
  obtain ⟨u, Y, h⟩ := exists_source_factor_of_bivector_symmetry X hr hsym
  exact ⟨u, Y, fun r k => h r.1 r.2 k⟩

/-- Appendix C, site 2: `A₂p=0` forces a common one-dimensional second-site source factor. -/
theorem exists_source_factor₂_of_siteAnti₂_bivec_eq_zero
    (X : Matrix (a × b × c) (Fin 2) ℂ) (hr : X.rank = 2)
    (hp : siteAnti₂ (bivecMat X) = 0) :
    ∃ (u : b → ℂ) (Y : Matrix (a × c) (Fin 2) ℂ),
      ∀ r k, X r k = u r.2.1 * Y (r.1, r.2.2) k := by
  let Z : Matrix (b × a × c) (Fin 2) ℂ := X.submatrix siteEquiv₂ (Equiv.refl (Fin 2))
  have hrZ : Z.rank = 2 := (Matrix.rank_submatrix X siteEquiv₂ (Equiv.refl (Fin 2))).trans hr
  have hsym : ∀ i j (r s : a × c), sourceDet (Z (i, r)) (Z (j, s)) =
      sourceDet (Z (j, r)) (Z (i, s)) := by
    intro i j r s
    have he := congrFun (congrFun hp (r.1, i, r.2)) (s.1, j, s.2)
    simp only [siteAnti₂, Matrix.of_apply, siteSwap₂, Equiv.coe_fn_mk, bivecMat_apply,
      Matrix.zero_apply] at he
    have hz : (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) *
        (sourceDet (Z (i, r)) (Z (j, s)) - sourceDet (Z (j, r)) (Z (i, s))) = 0 := by
      simp only [sourceDet, Z, Matrix.submatrix_apply, siteEquiv₂, Equiv.coe_fn_mk,
        Equiv.refl_apply]
      linear_combination 2 * he
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left inv_sqrt_two_complex_ne_zero)
  obtain ⟨u, Y, h⟩ := exists_source_factor_of_bivector_symmetry Z hrZ hsym
  exact ⟨u, Y, fun r k => h r.2.1 (r.1, r.2.2) k⟩

/-- Appendix C, site 3: `A₃p=0` forces a common one-dimensional third-site source factor. -/
theorem exists_source_factor₃_of_siteAnti₃_bivec_eq_zero
    (X : Matrix (a × b × c) (Fin 2) ℂ) (hr : X.rank = 2)
    (hp : siteAnti₃ (bivecMat X) = 0) :
    ∃ (u : c → ℂ) (Y : Matrix (a × b) (Fin 2) ℂ),
      ∀ r k, X r k = u r.2.2 * Y (r.1, r.2.1) k := by
  let Z : Matrix (c × a × b) (Fin 2) ℂ := X.submatrix siteEquiv₃ (Equiv.refl (Fin 2))
  have hrZ : Z.rank = 2 := (Matrix.rank_submatrix X siteEquiv₃ (Equiv.refl (Fin 2))).trans hr
  have hsym : ∀ i j (r s : a × b), sourceDet (Z (i, r)) (Z (j, s)) =
      sourceDet (Z (j, r)) (Z (i, s)) := by
    intro i j r s
    have he := congrFun (congrFun hp (r.1, r.2, i)) (s.1, s.2, j)
    simp only [siteAnti₃, Matrix.of_apply, siteSwap₃, Equiv.coe_fn_mk, bivecMat_apply,
      Matrix.zero_apply] at he
    have hz : (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) *
        (sourceDet (Z (i, r)) (Z (j, s)) - sourceDet (Z (j, r)) (Z (i, s))) = 0 := by
      simp only [sourceDet, Z, Matrix.submatrix_apply, siteEquiv₃, Equiv.coe_fn_mk,
        Equiv.refl_apply]
      linear_combination 2 * he
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left inv_sqrt_two_complex_ne_zero)
  obtain ⟨u, Y, h⟩ := exists_source_factor_of_bivector_symmetry Z hrZ hsym
  exact ⟨u, Y, fun r k => h r.2.2 (r.1, r.2.1) k⟩

end LocalAntisymmetry

section LocalRange

variable {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]

/-- A fixed local range vector makes the reduced range matrix have rank at most one. -/
theorem localRangeDim₁_le_one_of_range_factor
    (C : Matrix (a × b × c) (a × b × c) ℂ) (u : a → ℂ)
    (K : Matrix (b × c) (a × b × c) ℂ) (hC : ∀ r s, C r s = u r.1 * K r.2 s) :
    localRangeDim₁ C ≤ 1 := by
  unfold localRangeDim₁
  apply (rank_le_iff_exists_mul _ 1).mpr
  refine ⟨Matrix.of fun i (_ : Fin 1) => u i,
    Matrix.of fun (_ : Fin 1) j => ∑ l : b, ∑ k : c, ∑ s, K (l, k) s * star (C (j, l, k) s), ?_⟩
  ext i j
  simp only [ptrace₂₃, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
    Fin.sum_univ_one, hC, map_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro s _
  ring

theorem localRangeDim₂_le_one_of_range_factor
    (C : Matrix (a × b × c) (a × b × c) ℂ) (u : b → ℂ)
    (K : Matrix (a × c) (a × b × c) ℂ)
    (hC : ∀ r s, C r s = u r.2.1 * K (r.1, r.2.2) s) : localRangeDim₂ C ≤ 1 := by
  unfold localRangeDim₂
  apply (rank_le_iff_exists_mul _ 1).mpr
  refine ⟨Matrix.of fun i (_ : Fin 1) => u i,
    Matrix.of fun (_ : Fin 1) j => ∑ l : a, ∑ k : c, ∑ s, K (l, k) s * star (C (l, j, k) s), ?_⟩
  ext i j
  simp only [ptrace₁₃, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
    Fin.sum_univ_one, hC, map_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro s _
  ring

theorem localRangeDim₃_le_one_of_range_factor
    (C : Matrix (a × b × c) (a × b × c) ℂ) (u : c → ℂ)
    (K : Matrix (a × b) (a × b × c) ℂ)
    (hC : ∀ r s, C r s = u r.2.2 * K (r.1, r.2.1) s) : localRangeDim₃ C ≤ 1 := by
  unfold localRangeDim₃
  apply (rank_le_iff_exists_mul _ 1).mpr
  refine ⟨Matrix.of fun i (_ : Fin 1) => u i,
    Matrix.of fun (_ : Fin 1) j => ∑ l : a, ∑ k : b, ∑ s, K (l, k) s * star (C (l, k, j) s), ?_⟩
  ext i j
  simp only [ptrace₁₂, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
    Fin.sum_univ_one, hC, map_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro s _
  ring

/-- Appendix C: `A₁p=0` forces local range dimension at most one. -/
theorem localRangeDim₁_le_one_of_siteAnti₁_bivec_eq_zero
    (X : Matrix (a × b × c) (Fin 2) ℂ) (B : Matrix (Fin 2) (a × b × c) ℂ)
    (hr : (X * B).rank = 2) (hp : siteAnti₁ (bivecMat X) = 0) :
    localRangeDim₁ (X * B) ≤ 1 := by
  obtain ⟨u, Y, hX⟩ := exists_source_factor₁_of_siteAnti₁_bivec_eq_zero X
    (rank_eq_two_of_mul X B hr).1 hp
  apply localRangeDim₁_le_one_of_range_factor (X * B) u (Y * B)
  intro r s
  simp only [Matrix.mul_apply, hX, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem localRangeDim₂_le_one_of_siteAnti₂_bivec_eq_zero
    (X : Matrix (a × b × c) (Fin 2) ℂ) (B : Matrix (Fin 2) (a × b × c) ℂ)
    (hr : (X * B).rank = 2) (hp : siteAnti₂ (bivecMat X) = 0) :
    localRangeDim₂ (X * B) ≤ 1 := by
  obtain ⟨u, Y, hX⟩ := exists_source_factor₂_of_siteAnti₂_bivec_eq_zero X
    (rank_eq_two_of_mul X B hr).1 hp
  apply localRangeDim₂_le_one_of_range_factor (X * B) u (Y * B)
  intro r s
  simp only [Matrix.mul_apply, hX, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem localRangeDim₃_le_one_of_siteAnti₃_bivec_eq_zero
    (X : Matrix (a × b × c) (Fin 2) ℂ) (B : Matrix (Fin 2) (a × b × c) ℂ)
    (hr : (X * B).rank = 2) (hp : siteAnti₃ (bivecMat X) = 0) :
    localRangeDim₃ (X * B) ≤ 1 := by
  obtain ⟨u, Y, hX⟩ := exists_source_factor₃_of_siteAnti₃_bivec_eq_zero X
    (rank_eq_two_of_mul X B hr).1 hp
  apply localRangeDim₃_le_one_of_range_factor (X * B) u (Y * B)
  intro r s
  simp only [Matrix.mul_apply, hX, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- In particular, full local qutrit support makes each `Aᵢp` nonzero. The stronger
statement here only requires each local range dimension to exceed one. -/
theorem siteAnti_bivec_ne_zero_of_localRangeDim_gt_one
    (X : Matrix (a × b × c) (Fin 2) ℂ) (B : Matrix (Fin 2) (a × b × c) ℂ)
    (hr : (X * B).rank = 2) (h1 : 1 < localRangeDim₁ (X * B))
    (h2 : 1 < localRangeDim₂ (X * B)) (h3 : 1 < localRangeDim₃ (X * B)) :
    siteAnti₁ (bivecMat X) ≠ 0 ∧ siteAnti₂ (bivecMat X) ≠ 0 ∧ siteAnti₃ (bivecMat X) ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro hp
    exact (not_le_of_gt h1) (localRangeDim₁_le_one_of_siteAnti₁_bivec_eq_zero X B hr hp)
  · intro hp
    exact (not_le_of_gt h2) (localRangeDim₂_le_one_of_siteAnti₂_bivec_eq_zero X B hr hp)
  · intro hp
    exact (not_le_of_gt h3) (localRangeDim₃_le_one_of_siteAnti₃_bivec_eq_zero X B hr hp)

end LocalRange

end ThreeCopyQutritWerner

end
