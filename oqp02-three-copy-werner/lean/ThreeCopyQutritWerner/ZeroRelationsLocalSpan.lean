module

public import ThreeCopyQutritWerner.ZeroRelationsRankTwo
public import ThreeCopyQutritWerner.ZeroRelationsSupport

@[expose] public section


/-!
# Appendix C: local spans of a symmetric rank-two feature

The mixed-minor relation for `x yᵀ+y xᵀ` forces the local slices of `x` and `y` into a
common two-dimensional space. The first lemma isolates the elementary wedge calculation:
if `u ∧ b = a ∧ v` and `a,b` are independent, then `u,v ∈ span(a,b)`.
-/

noncomputable section

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

/-- The two explicit coordinates forced by `u ∧ b = a ∧ v` in an independent plane. -/
theorem exists_pair_coordinates_of_wedge_relation {ι : Type*}
    (a b u v : ι → ℂ) (p q : ι) (hd : a p * b q - a q * b p ≠ 0)
    (h : ∀ i j, u i * b j - u j * b i = a i * v j - a j * v i) :
    ∃ α β γ δ : ℂ, (∀ i, u i = a i * α + b i * β) ∧
      (∀ i, v i = a i * γ + b i * δ) := by
  let d := a p * b q - a q * b p
  refine ⟨(u p * b q - u q * b p) / d, (a p * u q - a q * u p) / d,
    (v p * b q - v q * b p) / d, (a p * v q - a q * v p) / d, ?_, ?_⟩
  · intro i
    -- Combine the three minor equations before dividing by the pivot minor.
    have he : d * u i = a i * (u p * b q - u q * b p) +
        b i * (a p * u q - a q * u p) := by
      dsimp [d]
      linear_combination a q * h p i - a p * h q i - a i * h p q
    calc
      u i = (a i * (u p * b q - u q * b p) +
          b i * (a p * u q - a q * u p)) / d :=
        (eq_div_iff (show d ≠ 0 from hd)).mpr (by simpa only [mul_comm] using he)
      _ = _ := by ring
  · intro i
    have he : d * v i = a i * (v p * b q - v q * b p) +
        b i * (a p * v q - a q * v p) := by
      dsimp [d]
      linear_combination -b q * h p i + b p * h q i + b i * h p q
    calc
      v i = (a i * (v p * b q - v q * b p) +
          b i * (a p * v q - a q * v p)) / d :=
        (eq_div_iff (show d ≠ 0 from hd)).mpr (by simpa only [mul_comm] using he)
      _ = _ := by ring

/-- A family of wedge relations gives a common local plane with explicit scalar coordinates. -/
theorem exists_common_plane_of_wedge_relation {ι r : Type*}
    (x y : ι → r → ℂ) (a b : ι → ℂ) (p q : ι)
    (hd : a p * b q - a q * b p ≠ 0)
    (h : ∀ i j s, x i s * b j - x j s * b i = a i * y j s - a j * y i s) :
    ∃ (α β γ δ : r → ℂ),
      (∀ i s, x i s = a i * α s + b i * β s) ∧
      (∀ i s, y i s = a i * γ s + b i * δ s) := by
  classical
  have hh := fun s => exists_pair_coordinates_of_wedge_relation a b
    (fun i => x i s) (fun i => y i s) p q hd (fun i j => h i j s)
  choose α β γ δ hx hy using hh
  exact ⟨α, β, γ, δ, fun i s => hx s i, fun i s => hy s i⟩

/-- The mixed minors of a locally symmetric rank-two feature force its two defining
vectors into a common local plane. Nonzero hypotheses exclude a zero feature whose unused
factor can have arbitrary local support. -/
theorem exists_common_local_plane_of_mixed_minors {ι r : Type*}
    (x y : ι → r → ℂ) (hx : ∃ i s, x i s ≠ 0) (hy : ∃ i s, y i s ≠ 0)
    (hm : ∀ i j s t, x i s * y j t - x j s * y i t =
      x i t * y j s - x j t * y i s) :
    ∃ (a b : ι → ℂ) (α β γ δ : r → ℂ),
      (∀ i s, x i s = a i * α s + b i * β s) ∧
      (∀ i s, y i s = a i * γ s + b i * δ s) := by
  classical
  by_cases hd : ∃ p q s, x p s * y q s - x q s * y p s ≠ 0
  · obtain ⟨p, q, s, hd⟩ := hd
    obtain ⟨α, β, γ, δ, h₁, h₂⟩ := exists_common_plane_of_wedge_relation x y
      (fun i => x i s) (fun i => y i s) p q hd (fun i j t => hm i j t s)
    exact ⟨fun i => x i s, fun i => y i s, α, β, γ, δ, h₁, h₂⟩
  push_neg at hd
  by_cases hc : ∃ p q s t, x p s * y q t - x q s * y p t ≠ 0
  · obtain ⟨p, q, s, t, hc⟩ := hc
    let a := fun i => x i s + x i t
    let b := fun i => y i s + y i t
    have hab : a p * b q - a q * b p ≠ 0 := by
      intro hz
      apply hc
      dsimp [a, b] at hz
      linear_combination (hz - hd p q s - hd p q t + hm p q s t) / 2
    have hmab : ∀ i j u, x i u * b j - x j u * b i =
        a i * y j u - a j * y i u := by
      intro i j u
      dsimp [a, b]
      linear_combination hm i j u s + hm i j u t
    obtain ⟨α, β, γ, δ, h₁, h₂⟩ :=
      exists_common_plane_of_wedge_relation x y a b p q hab hmab
    exact ⟨a, b, α, β, γ, δ, h₁, h₂⟩
  push_neg at hc
  obtain ⟨p, s, hxp⟩ := hx
  obtain ⟨q, t, hyq⟩ := hy
  refine ⟨fun i => y i t, 0, fun u => x q u / y q t, 0,
    fun u => x q s * y p u / (y q t * x p s), 0, ?_, ?_⟩
  · intro i u
    change x i u = y i t * (x q u / y q t) + 0 * 0
    field_simp [hyq]
    linear_combination hc i q u t
  · intro i u
    change y i u = y i t * (x q s * y p u / (y q t * x p s)) + 0 * 0
    field_simp [hyq, hxp]
    linear_combination y q t * hc p i s u + y p u * hc i q s t

section LocalSupport

variable {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]

/-- An explicit two-dimensional local range factor bounds the actual reduced support. -/
theorem localRangeDim₁_le_two_of_range_plane
    (C : Matrix (a × b × c) (a × b × c) ℂ) (u v : a → ℂ)
    (K L : Matrix (b × c) (a × b × c) ℂ)
    (hC : ∀ i r s, C (i, r) s = u i * K r s + v i * L r s) :
    localRangeDim₁ C ≤ 2 := by
  unfold localRangeDim₁
  apply (rank_le_iff_exists_mul _ 2).mpr
  refine ⟨Matrix.of fun i k => ![u i, v i] k,
    Matrix.of fun k j => ![∑ l : b, ∑ m : c, ∑ s, K (l, m) s * star (C (j, l, m) s),
      ∑ l : b, ∑ m : c, ∑ s, L (l, m) s * star (C (j, l, m) s)] k, ?_⟩
  ext i j
  simp only [ptrace₂₃, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
    Fin.sum_univ_two]
  change (∑ l : b, ∑ m : c, ∑ s, C (i, l, m) s * star (C (j, l, m) s)) =
    u i * (∑ l : b, ∑ m : c, ∑ s, K (l, m) s * star (C (j, l, m) s)) +
    v i * (∑ l : b, ∑ m : c, ∑ s, L (l, m) s * star (C (j, l, m) s))
  calc
    _ = ∑ l : b, ∑ m : c, ∑ s,
        (u i * K (l, m) s + v i * L (l, m) s) * star (C (j, l, m) s) := by
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro m _
      apply Finset.sum_congr rfl
      intro s _
      rw [hC i (l, m) s]
    _ = _ := by
      simp only [add_mul, mul_assoc, Finset.sum_add_distrib, Finset.mul_sum]

/-- A nonzero locally symmetric symmetrized product has a common local plane. -/
theorem exists_range_plane_of_local_symmetry_symmetrized
    (H : Matrix (a × b × c) (a × b × c) ℂ) (h0 : H ≠ 0)
    (x y : a × b × c → ℂ)
    (hf : ∀ r s, H r s = x r * y s + y r * x s) (h1 : siteAnti₁ H = 0) :
    ∃ (u v : a → ℂ) (K L : Matrix (b × c) (a × b × c) ℂ),
      ∀ i r s, H (i, r) s = u i * K r s + v i * L r s := by
  classical
  have hx : ∃ i r, x (i, r) ≠ 0 := by
    by_contra hn
    push_neg at hn
    have hx0 : ∀ r, x r = 0 := fun r => hn r.1 r.2
    apply h0
    ext r s
    simp only [hf, hx0, zero_mul, mul_zero, add_zero, Matrix.zero_apply]
  have hy : ∃ i r, y (i, r) ≠ 0 := by
    by_contra hn
    push_neg at hn
    have hy0 : ∀ r, y r = 0 := fun r => hn r.1 r.2
    apply h0
    ext r s
    simp only [hf, hy0, zero_mul, mul_zero, add_zero, Matrix.zero_apply]
  have hm : ∀ i j r s, x (i, r) * y (j, s) - x (j, r) * y (i, s) =
      x (i, s) * y (j, r) - x (j, s) * y (i, r) := by
    intro i j r s
    have he := congrFun (congrFun h1 (i, r)) (j, s)
    simp only [siteAnti₁, Matrix.of_apply, siteSwap₁, Equiv.coe_fn_mk, hf,
      Matrix.zero_apply] at he
    linear_combination 2 * he
  obtain ⟨u, v, α, β, γ, δ, hX, hY⟩ := exists_common_local_plane_of_mixed_minors
    (fun i r => x (i, r)) (fun i r => y (i, r)) hx hy hm
  refine ⟨u, v, Matrix.of fun r s => α r * y s + γ r * x s,
    Matrix.of fun r s => β r * y s + δ r * x s, ?_⟩
  intro i r s
  rw [hf, hX i r, hY i r]
  simp only [Matrix.of_apply]
  ring

/-- Multiplying on the right preserves an explicit local range plane. -/
theorem localRangeDim₁_le_two_of_mul_range_plane
    (H M : Matrix (a × b × c) (a × b × c) ℂ)
    (u v : a → ℂ) (K L : Matrix (b × c) (a × b × c) ℂ)
    (hH : ∀ i r s, H (i, r) s = u i * K r s + v i * L r s) :
    localRangeDim₁ (H * M) ≤ 2 := by
  apply localRangeDim₁_le_two_of_range_plane (H * M) u v (K * M) (L * M)
  intro i r s
  simp only [Matrix.mul_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  rw [hH]
  ring

/-- The rank-two branch of Appendix C: local symmetry of `H` forces a thin local source.
This conclusion is independent of the analytic endpoint-equality inputs. -/
theorem localRangeDim₁_le_two_of_hFeature_rank_two
    (X : Matrix (a × b × c) (Fin 2) ℂ) (B : Matrix (Fin 2) (a × b × c) ℂ)
    (hr : (hFeature (X * B) (bivecMat X)).rank = 2)
    (h1 : siteAnti₁ (hFeature (X * B) (bivecMat X)) = 0) :
    localRangeDim₁ (X * B) ≤ 2 := by
  let H := hFeature (X * B) (bivecMat X)
  change H.rank = 2 at hr
  have h0 : H ≠ 0 := by
    intro hz
    have : H.rank = 0 := by rw [hz, Matrix.rank_zero]
    omega
  obtain ⟨x, y, hxy⟩ := exists_symmetrized_factor_of_rank_two H hr (hFeature_transpose X B)
  obtain ⟨u, v, K, L, hH⟩ := exists_range_plane_of_local_symmetry_symmetrized H h0 x y hxy h1
  obtain ⟨M, hM⟩ := eq_hFeature_mul_of_rank_two X B hr
  rw [hM]
  exact localRangeDim₁_le_two_of_mul_range_plane H M u v K L hH

end LocalSupport

end ThreeCopyQutritWerner

end
