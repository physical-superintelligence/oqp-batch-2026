module

public import CausalNonpurifiability.Linear.Indices
public import CausalNonpurifiability.Linear.PartialTrace
public import CausalNonpurifiability.Linear.Positive

@[expose] public section


/-!
# `CausalNonpurifiability.Linear.Spectral`

Finite spectral calculus for Hermitian and positive matrices, and support annihilation
(manuscript §9: in `eq:ordered-channel` `ρ^{-1/2}` is the inverse of `ρ^{1/2}` on the support of
`ρ`; `Ŵ` vanishes on `ker ρ ⊗ A_O ⊗ B_I`).

The definitions `specMap`, `sqrtPSD`, `pinvSqrt`, `suppProj` are **verbatim copies** of the
definitions in `Boundary/Dilation` (hence definitionally identical), and the
lemma names and statement shapes coincide with the stubs there, so that `Boundary/Dilation` can
`import CausalNonpurifiability.Linear.Spectral` and drop its local §2/§3.

Route: `specMap hA f = U · diag (f ∘ λ) · Uᴴ` with `U = hA.eigenvectorUnitary`; the algebra of
`specMap` is the algebra of the diagonal (`Matrix.diagonal_mul_diagonal`), using only
`Uᴴ U = U Uᴴ = 1` (`Matrix.UnitaryGroup`) and the eigen-equation
`Matrix.IsHermitian.mulVec_eigenvectorBasis` for `specMap_id` (no continuous functional
calculus needed).  Support annihilation is the standard consequence of
`Matrix.PosSemidef.dotProduct_mulVec_zero_iff`: the quadratic form of `M ≥ 0` on
`v ⊗ e_w` summed over `w` is the quadratic form of `Tr_Y M` on `v`.
-/

set_option autoImplicit false

open scoped Kronecker ComplexOrder Matrix

namespace CausalNonpurifiability

noncomputable section

/-! ### Spectral calculus for Hermitian and positive matrices -/

section Spectral

variable {n : Type} [Fintype n] [DecidableEq n] {A M : Matrix n n ℂ}

/-- `f(A) = U diag(f ∘ eigenvalues) Uᴴ` for Hermitian `A` (finite functional calculus through
the spectral theorem). -/
def specMap (hA : A.IsHermitian) (f : ℝ → ℝ) : Matrix n n ℂ :=
  (hA.eigenvectorUnitary : Matrix n n ℂ) *
    Matrix.diagonal (fun i => ((f (hA.eigenvalues i) : ℝ) : ℂ)) *
      (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ

/-- `Uᴴ U = 1` for the eigenvector unitary. -/
theorem eigenvectorUnitary_conjTranspose_mul (hA : A.IsHermitian) :
    (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ * (hA.eigenvectorUnitary : Matrix n n ℂ) = 1 := by
  have h := Matrix.UnitaryGroup.star_mul_self hA.eigenvectorUnitary
  rwa [Matrix.star_eq_conjTranspose] at h

/-- `U Uᴴ = 1` for the eigenvector unitary. -/
theorem eigenvectorUnitary_mul_conjTranspose (hA : A.IsHermitian) :
    (hA.eigenvectorUnitary : Matrix n n ℂ) * (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ = 1 := by
  have h := Matrix.mem_unitaryGroup_iff.mp hA.eigenvectorUnitary.2
  rwa [Matrix.star_eq_conjTranspose] at h

/-- The eigen-equation in matrix form: `A U = U diag(λ)`. -/
theorem mul_eigenvectorUnitary (hA : A.IsHermitian) :
    A * (hA.eigenvectorUnitary : Matrix n n ℂ)
      = (hA.eigenvectorUnitary : Matrix n n ℂ) *
          Matrix.diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) := by
  ext i j
  have h := congrFun (hA.mulVec_eigenvectorBasis j) i
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, Complex.real_smul] at h
  rw [Matrix.mul_apply, Matrix.mul_diagonal]
  simp only [Matrix.IsHermitian.eigenvectorUnitary_apply]
  rw [h, mul_comm]

theorem specMap_mul (hA : A.IsHermitian) (f g : ℝ → ℝ) :
    specMap hA f * specMap hA g = specMap hA (fun x => f x * g x) := by
  unfold specMap
  simp only [Matrix.mul_assoc, Complex.ofReal_mul]
  rw [← Matrix.mul_assoc (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ,
    eigenvectorUnitary_conjTranspose_mul, Matrix.one_mul, ← Matrix.mul_assoc (Matrix.diagonal _),
    Matrix.diagonal_mul_diagonal]

theorem specMap_congr (hA : A.IsHermitian) {f g : ℝ → ℝ}
    (h : ∀ i, f (hA.eigenvalues i) = g (hA.eigenvalues i)) : specMap hA f = specMap hA g := by
  unfold specMap
  simp only [h]

theorem specMap_id (hA : A.IsHermitian) : specMap hA (fun x => x) = A := by
  unfold specMap
  rw [← mul_eigenvectorUnitary, Matrix.mul_assoc, eigenvectorUnitary_mul_conjTranspose,
    Matrix.mul_one]

theorem specMap_one (hA : A.IsHermitian) : specMap hA (fun _ => 1) = 1 := by
  unfold specMap
  simp only [Complex.ofReal_one, Matrix.diagonal_one, Matrix.mul_one]
  exact eigenvectorUnitary_mul_conjTranspose hA

theorem specMap_zero (hA : A.IsHermitian) : specMap hA (fun _ => 0) = 0 := by
  unfold specMap
  simp only [Complex.ofReal_zero, Matrix.diagonal_zero, Matrix.mul_zero, Matrix.zero_mul]

theorem specMap_sub (hA : A.IsHermitian) (f g : ℝ → ℝ) :
    specMap hA (fun x => f x - g x) = specMap hA f - specMap hA g := by
  unfold specMap
  simp only [Complex.ofReal_sub]
  rw [← Matrix.diagonal_sub, Matrix.mul_sub, Matrix.sub_mul]

theorem specMap_isHermitian (hA : A.IsHermitian) (f : ℝ → ℝ) : (specMap hA f).IsHermitian := by
  have hD : (Matrix.diagonal (fun i => ((f (hA.eigenvalues i) : ℝ) : ℂ))).IsHermitian :=
    Matrix.isHermitian_diagonal_iff.mpr fun i => isSelfAdjoint_iff.mpr (Complex.conj_ofReal _)
  unfold specMap
  show ((hA.eigenvectorUnitary : Matrix n n ℂ) * _ * (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ)ᴴ = _
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    hD.eq, Matrix.mul_assoc]

theorem specMap_posSemidef (hA : A.IsHermitian) {f : ℝ → ℝ} (hf : ∀ x, 0 ≤ f x) :
    (specMap hA f).PosSemidef := by
  unfold specMap
  exact (Matrix.PosSemidef.diagonal fun i => Complex.zero_le_real.mpr (hf _)).mul_mul_conjTranspose_same _

/-- `f(A) · A = (f · id)(A)`. -/
theorem specMap_mul_self (hA : A.IsHermitian) (f : ℝ → ℝ) :
    specMap hA f * A = specMap hA (fun x => f x * x) := by
  rw [← specMap_mul, specMap_id]

/-- `A · f(A) = (id · f)(A)`. -/
theorem self_mul_specMap (hA : A.IsHermitian) (f : ℝ → ℝ) :
    A * specMap hA f = specMap hA (fun x => x * f x) := by
  rw [← specMap_mul, specMap_id]

/-- Every positive matrix is a Gram matrix `B Bᴴ` (take `B = M^{1/2}`). -/
theorem psd_eq_mul_conjTranspose (hM : M.PosSemidef) : ∃ B : Matrix n n ℂ, M = B * Bᴴ :=
  ⟨specMap hM.1 Real.sqrt, by
    rw [(specMap_isHermitian hM.1 Real.sqrt).eq, specMap_mul]
    exact ((specMap_congr hM.1 (f := fun x => Real.sqrt x * Real.sqrt x) (g := fun x => x)
      (fun i => Real.mul_self_sqrt (hM.eigenvalues_nonneg i))).trans (specMap_id hM.1)).symm⟩

/-- The positive square root `ρ^{1/2}`. -/
def sqrtPSD (hM : M.PosSemidef) : Matrix n n ℂ := specMap hM.1 Real.sqrt

/-- The pseudo-inverse square root `ρ^{-1/2}` (zero on the kernel; in `eq:ordered-channel` it is
the inverse of `ρ^{1/2}` on the support of `ρ`). -/
def pinvSqrt (hM : M.PosSemidef) : Matrix n n ℂ := specMap hM.1 (fun x => (Real.sqrt x)⁻¹)

/-- The support projector of a positive matrix. -/
def suppProj (hM : M.PosSemidef) : Matrix n n ℂ := specMap hM.1 (fun x => if x = 0 then 0 else 1)

/-! Pointwise real facts on nonnegative eigenvalues. -/

theorem real_sqrt_mul_inv_sqrt {x : ℝ} (hx : 0 ≤ x) :
    Real.sqrt x * (Real.sqrt x)⁻¹ = if x = 0 then 0 else 1 := by
  split_ifs with h
  · simp [h]
  · exact mul_inv_cancel₀ (Real.sqrt_ne_zero'.mpr (lt_of_le_of_ne hx (Ne.symm h)))

theorem real_inv_sqrt_mul_sqrt {x : ℝ} (hx : 0 ≤ x) :
    (Real.sqrt x)⁻¹ * Real.sqrt x = if x = 0 then 0 else 1 := by
  split_ifs with h
  · simp [h]
  · exact inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr (lt_of_le_of_ne hx (Ne.symm h)))

theorem real_inv_sqrt_mul_self_mul_inv_sqrt {x : ℝ} (hx : 0 ≤ x) :
    (Real.sqrt x)⁻¹ * x * (Real.sqrt x)⁻¹ = if x = 0 then 0 else 1 := by
  split_ifs with h
  · simp [h]
  · have hs : Real.sqrt x ≠ 0 := Real.sqrt_ne_zero'.mpr (lt_of_le_of_ne hx (Ne.symm h))
    calc (Real.sqrt x)⁻¹ * x * (Real.sqrt x)⁻¹
        = (Real.sqrt x)⁻¹ * (Real.sqrt x * Real.sqrt x) * (Real.sqrt x)⁻¹ := by
          rw [Real.mul_self_sqrt hx]
      _ = 1 := by rw [inv_mul_cancel_left₀ hs, mul_inv_cancel₀ hs]

theorem real_sqrt_mul_one_sub_ind (x : ℝ) :
    Real.sqrt x * (1 - if x = 0 then 0 else 1) = 0 := by
  split_ifs with h
  · simp [h]
  · simp

theorem real_self_mul_one_sub_ind (x : ℝ) : x * (1 - if x = 0 then 0 else 1) = 0 := by
  split_ifs with h
  · simp [h]
  · simp

theorem sqrtPSD_mul_self (hM : M.PosSemidef) : sqrtPSD hM * sqrtPSD hM = M := by
  unfold sqrtPSD
  rw [specMap_mul, specMap_congr hM.1 (f := fun x => Real.sqrt x * Real.sqrt x) (g := fun x => x)
    (fun i => Real.mul_self_sqrt (hM.eigenvalues_nonneg i)), specMap_id]

theorem sqrtPSD_isHermitian (hM : M.PosSemidef) : (sqrtPSD hM).IsHermitian :=
  specMap_isHermitian _ _

theorem sqrtPSD_posSemidef (hM : M.PosSemidef) : (sqrtPSD hM).PosSemidef :=
  specMap_posSemidef _ fun _ => Real.sqrt_nonneg _

theorem pinvSqrt_isHermitian (hM : M.PosSemidef) : (pinvSqrt hM).IsHermitian :=
  specMap_isHermitian _ _

theorem suppProj_isHermitian (hM : M.PosSemidef) : (suppProj hM).IsHermitian :=
  specMap_isHermitian _ _

theorem suppProj_posSemidef (hM : M.PosSemidef) : (suppProj hM).PosSemidef := by
  unfold suppProj
  exact specMap_posSemidef _ fun x => by split_ifs <;> norm_num

/-- `1 − Π_ρ = (1 − 1_{≠0})(ρ)`. -/
theorem one_sub_suppProj_eq (hM : M.PosSemidef) :
    (1 : Matrix n n ℂ) - suppProj hM = specMap hM.1 (fun x => 1 - if x = 0 then 0 else 1) := by
  unfold suppProj
  rw [specMap_sub, specMap_one]

theorem one_sub_suppProj_posSemidef (hM : M.PosSemidef) : (1 - suppProj hM).PosSemidef := by
  rw [one_sub_suppProj_eq]
  exact specMap_posSemidef _ fun x => by split_ifs <;> norm_num

theorem pinvSqrt_mul_self_mul_pinvSqrt (hM : M.PosSemidef) :
    pinvSqrt hM * M * pinvSqrt hM = suppProj hM := by
  unfold pinvSqrt suppProj
  rw [specMap_mul_self, specMap_mul]
  exact specMap_congr hM.1 fun i => real_inv_sqrt_mul_self_mul_inv_sqrt (hM.eigenvalues_nonneg i)

theorem sqrtPSD_mul_pinvSqrt (hM : M.PosSemidef) : sqrtPSD hM * pinvSqrt hM = suppProj hM := by
  unfold sqrtPSD pinvSqrt suppProj
  rw [specMap_mul]
  exact specMap_congr hM.1 fun i => real_sqrt_mul_inv_sqrt (hM.eigenvalues_nonneg i)

theorem pinvSqrt_mul_sqrtPSD (hM : M.PosSemidef) : pinvSqrt hM * sqrtPSD hM = suppProj hM := by
  unfold sqrtPSD pinvSqrt suppProj
  rw [specMap_mul]
  exact specMap_congr hM.1 fun i => real_inv_sqrt_mul_sqrt (hM.eigenvalues_nonneg i)

theorem sqrtPSD_mul_one_sub_suppProj (hM : M.PosSemidef) : sqrtPSD hM * (1 - suppProj hM) = 0 := by
  unfold sqrtPSD
  rw [one_sub_suppProj_eq, specMap_mul,
    specMap_congr hM.1 (g := fun _ => 0) (fun i => real_sqrt_mul_one_sub_ind _), specMap_zero]

theorem self_mul_one_sub_suppProj (hM : M.PosSemidef) : M * (1 - suppProj hM) = 0 := by
  rw [one_sub_suppProj_eq, self_mul_specMap,
    specMap_congr hM.1 (g := fun _ => 0) (fun i => real_self_mul_one_sub_ind _), specMap_zero]

end Spectral

/-! ### Support annihilation -/

section Support

variable {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

omit [DecidableEq X] in
/-- The quadratic form of `M` on `v ⊗ e_w` is the quadratic form of the `(w,w)` block on `v`. -/
theorem quad_kron_basis (M : Op (X × Y)) (v : X → ℂ) (w : Y) :
    star (fun p : X × Y => v p.1 * (if p.2 = w then 1 else 0)) ⬝ᵥ
        M *ᵥ (fun p : X × Y => v p.1 * (if p.2 = w then 1 else 0))
      = star v ⬝ᵥ (M.submatrix (fun x => (x, w)) (fun x => (x, w))) *ᵥ v := by
  simp only [dotProduct, Matrix.mulVec, Matrix.submatrix_apply, Pi.star_apply,
    Fintype.sum_prod_type, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, star_zero,
    apply_ite star, Finset.sum_ite_eq', Finset.mem_univ, if_true]

omit [DecidableEq X] [DecidableEq Y] in
/-- Summing the block quadratic forms over `w` gives the quadratic form of `Tr_Y M`. -/
theorem sum_quad_blocks (M : Op (X × Y)) (v : X → ℂ) :
    ∑ w, star v ⬝ᵥ (M.submatrix (fun x => (x, w)) (fun x => (x, w))) *ᵥ v
      = star v ⬝ᵥ (ptraceOut M) *ᵥ v := by
  simp only [dotProduct, Matrix.mulVec, Matrix.submatrix_apply, ptraceOut_apply, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_comm

omit [DecidableEq X] in
/-- If `M ≥ 0` on `X ⊗ Y` and `N = Tr_Y M` kills `v`, then `M` kills `v ⊗ e_w` for every basis
vector `e_w` (sum the nonnegative quadratic forms; `PosSemidef.dotProduct_mulVec_zero_iff`). -/
theorem psd_mulVec_kron_eq_zero {M : Op (X × Y)} (hM : M.PosSemidef) {N : Op X}
    (hN : ptraceOut M = N) {v : X → ℂ} (hv : N *ᵥ v = 0) (w : Y) :
    M *ᵥ (fun p : X × Y => v p.1 * (if p.2 = w then 1 else 0)) = 0 := by
  have hsum : ∑ w', star (fun p : X × Y => v p.1 * (if p.2 = w' then 1 else 0)) ⬝ᵥ
      M *ᵥ (fun p : X × Y => v p.1 * (if p.2 = w' then 1 else 0)) = 0 := by
    simp only [quad_kron_basis]
    rw [sum_quad_blocks, hN, hv, dotProduct_zero]
  have hnn : ∀ w' ∈ (Finset.univ : Finset Y),
      0 ≤ star (fun p : X × Y => v p.1 * (if p.2 = w' then 1 else 0)) ⬝ᵥ
        M *ᵥ (fun p : X × Y => v p.1 * (if p.2 = w' then 1 else 0)) :=
    fun w' _ => hM.dotProduct_mulVec_nonneg _
  have hw := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum w (Finset.mem_univ w)
  exact hM.dotProduct_mulVec_zero_iff.mp hw

omit [DecidableEq X] in
/-- `N * P = 0 ⇒ M * (P ⊗ I) = 0` for `M ≥ 0` with `Tr_Y M = N`. -/
theorem psd_mul_kron_eq_zero {M : Op (X × Y)} (hM : M.PosSemidef) {N : Op X}
    (hN : ptraceOut M = N) {P : Op X} (hP : N * P = 0) : M * (P ⊗ₖ (1 : Op Y)) = 0 := by
  ext p q
  have hv : N *ᵥ (fun x => P x q.1) = 0 := by
    funext x
    have h := congrFun (congrFun hP x) q.1
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using h
  have h := congrFun (psd_mulVec_kron_eq_zero hM hN hv q.2) p
  simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at h
  rw [Matrix.mul_apply, Matrix.zero_apply]
  simpa [Matrix.kroneckerMap_apply, Matrix.one_apply] using h

omit [Fintype X] [Fintype Y] [DecidableEq X] in
/-- `(Q ⊗ I)ᴴ = Q ⊗ I` for Hermitian `Q`. -/
theorem kronecker_one_conjTranspose {Q : Op X} (hQ : Q.IsHermitian) :
    (Q ⊗ₖ (1 : Op Y))ᴴ = Q ⊗ₖ (1 : Op Y) := by
  ext ⟨x, y⟩ ⟨x', y'⟩
  simp only [Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply, star_mul', hQ.apply,
    Matrix.one_apply]
  rcases eq_or_ne y y' with rfl | h
  · simp
  · simp [h, Ne.symm h]

/-- Support annihilation (manuscript §9: "The operator `Ŵ` vanishes on the
subspace `ker ρ ⊗ A_O ⊗ B_I`"): with
`Q := 1 - Π_ρ`, `M (Q ⊗ 1) = 0` and `(Q ⊗ 1) M = 0`, so `(Π_ρ ⊗ 1) M (Π_ρ ⊗ 1) = M`. -/
theorem support_annihilation {M : Op (X × Y)} (hM : M.PosSemidef) {N : Op X}
    (hNpsd : N.PosSemidef) (hN : ptraceOut M = N) :
    (suppProj hNpsd ⊗ₖ (1 : Op Y)) * M * (suppProj hNpsd ⊗ₖ (1 : Op Y)) = M := by
  have hR : M * (suppProj hNpsd ⊗ₖ (1 : Op Y)) = M := by
    have h0 := psd_mul_kron_eq_zero hM hN (self_mul_one_sub_suppProj hNpsd)
    rw [sub_kronecker', Matrix.one_kronecker_one, Matrix.mul_sub, Matrix.mul_one,
      sub_eq_zero] at h0
    exact h0.symm
  have hL : (suppProj hNpsd ⊗ₖ (1 : Op Y)) * M = M := by
    have h1 := congrArg Matrix.conjTranspose hR
    rwa [Matrix.conjTranspose_mul, hM.1.eq,
      kronecker_one_conjTranspose (suppProj_isHermitian hNpsd)] at h1
  rw [hL, hR]

end Support

end

end CausalNonpurifiability
