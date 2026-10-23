module

public import ThreeCopyQutritWerner.SharpPartialTraceAlgebra
public import ThreeCopyQutritWerner.ZeroReserveAlgebra

@[expose] public section


/-!
# The literal double-antisymmetric replica projection

`sharpDoubleAnti` is `(I-F_L)(I-F_R)/4` on the two replicas indexed by a
matrix. It is an orthogonal projection for the original Hilbert--Schmidt
pairing and has symmetric range. The two-ray estimate below retains the
original reshaped Gram matrices and the sharp factor one-half.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace ThreeCopyQutritWerner

section Projection

variable {L R : Type*}

/-- Exchange only the left coordinates of the matrix's two replica indices. -/
def sharpSwapLeft (X : Matrix (L × R) (L × R) ℂ) : Matrix (L × R) (L × R) ℂ :=
  fun i j => X (j.1, i.2) (i.1, j.2)

/-- Exchange only the right coordinates of the matrix's two replica indices. -/
def sharpSwapRight (X : Matrix (L × R) (L × R) ℂ) : Matrix (L × R) (L × R) ℂ :=
  fun i j => X (i.1, j.2) (j.1, i.2)

/-- The exact normalized product of the two local antisymmetrizers. -/
def sharpDoubleAnti (X : Matrix (L × R) (L × R) ℂ) : Matrix (L × R) (L × R) ℂ :=
  fun i j => (X i j - sharpSwapLeft X i j - sharpSwapRight X i j + X j i) / 4

theorem sharpDoubleAnti_add (X Y : Matrix (L × R) (L × R) ℂ) :
    sharpDoubleAnti (X + Y) = sharpDoubleAnti X + sharpDoubleAnti Y := by
  ext i j
  simp only [sharpDoubleAnti, sharpSwapLeft, sharpSwapRight, Matrix.add_apply]
  ring

theorem sharpDoubleAnti_smul (z : ℂ) (X : Matrix (L × R) (L × R) ℂ) :
    sharpDoubleAnti (z • X) = z • sharpDoubleAnti X := by
  ext i j
  simp only [sharpDoubleAnti, sharpSwapLeft, sharpSwapRight, Matrix.smul_apply, smul_eq_mul]
  ring

theorem sharpDoubleAnti_idempotent (X : Matrix (L × R) (L × R) ℂ) :
    sharpDoubleAnti (sharpDoubleAnti X) = sharpDoubleAnti X := by
  ext i j
  simp only [sharpDoubleAnti, sharpSwapLeft, sharpSwapRight]
  ring

/-- Two local odd swap parities imply ordinary transpose symmetry. -/
theorem sharpDoubleAnti_transpose (X : Matrix (L × R) (L × R) ℂ) :
    (sharpDoubleAnti X)ᵀ = sharpDoubleAnti X := by
  ext i j
  simp only [Matrix.transpose_apply, sharpDoubleAnti, sharpSwapLeft, sharpSwapRight]
  ring

variable [Fintype L] [Fintype R]

private theorem sharp_pairing_involution {I : Type*} [Fintype I]
    (e : I ≃ I) (he : ∀ i, e (e i) = i) (f g : I → ℂ) :
    (∑ i, conj (f (e i)) * g i) = ∑ i, conj (f i) * g (e i) := by
  apply Fintype.sum_equiv e
  intro i
  rw [he]

/-- Each local swap is selfadjoint for the literal finite matrix pairing. -/
theorem sharpSwapLeft_selfadjoint (X Y : Matrix (L × R) (L × R) ℂ) :
    hsInner (sharpSwapLeft X) Y = hsInner X (sharpSwapLeft Y) := by
  have h := sharp_pairing_involution (swapLeft (L := L) (R := R)) (fun _ => rfl)
    (fun p => X p.1 p.2) (fun p => Y p.1 p.2)
  simpa only [Fintype.sum_prod_type, hsInner, sharpSwapLeft, swapLeft, Equiv.coe_fn_mk] using h

theorem sharpSwapRight_selfadjoint (X Y : Matrix (L × R) (L × R) ℂ) :
    hsInner (sharpSwapRight X) Y = hsInner X (sharpSwapRight Y) := by
  have h := sharp_pairing_involution (swapRight (L := L) (R := R)) (fun _ => rfl)
    (fun p => X p.1 p.2) (fun p => Y p.1 p.2)
  simpa only [Fintype.sum_prod_type, hsInner, sharpSwapRight, swapRight, Equiv.coe_fn_mk] using h

theorem sharpTranspose_selfadjoint (X Y : Matrix (L × R) (L × R) ℂ) :
    hsInner Xᵀ Y = hsInner X Yᵀ := by
  have h := sharp_pairing_involution (Equiv.prodComm (L × R) (L × R)) (fun _ => rfl)
    (fun p => X p.1 p.2) (fun p => Y p.1 p.2)
  simpa only [Fintype.sum_prod_type, hsInner, Matrix.transpose_apply,
    Equiv.prodComm_apply, Prod.swap_prod_mk] using h

private theorem sharpDoubleAnti_pairing_left (X Y : Matrix (L × R) (L × R) ℂ) :
    4 * hsInner (sharpDoubleAnti X) Y =
      hsInner X Y - hsInner (sharpSwapLeft X) Y - hsInner (sharpSwapRight X) Y +
        hsInner Xᵀ Y := by
  simp only [hsInner, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [sharpDoubleAnti, Matrix.transpose_apply, map_div₀, map_add, map_sub, map_ofNat]
  ring

private theorem sharpDoubleAnti_pairing_right (X Y : Matrix (L × R) (L × R) ℂ) :
    4 * hsInner X (sharpDoubleAnti Y) =
      hsInner X Y - hsInner X (sharpSwapLeft Y) - hsInner X (sharpSwapRight Y) +
        hsInner X Yᵀ := by
  simp only [hsInner, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [sharpDoubleAnti, Matrix.transpose_apply]
  ring

/-- The product of commuting replica antisymmetrizers is Hilbert--Schmidt selfadjoint. -/
theorem sharpDoubleAnti_selfadjoint (X Y : Matrix (L × R) (L × R) ℂ) :
    hsInner (sharpDoubleAnti X) Y = hsInner X (sharpDoubleAnti Y) := by
  have hL := sharpDoubleAnti_pairing_left X Y
  have hR := sharpDoubleAnti_pairing_right X Y
  rw [sharpSwapLeft_selfadjoint, sharpSwapRight_selfadjoint, sharpTranspose_selfadjoint] at hL
  linear_combination (hL - hR) / 4

/-- The orthogonal-projection norm is the original pairing with the projected vector. -/
theorem sharpDoubleAnti_frobSq (X : Matrix (L × R) (L × R) ℂ) :
    frobSq (sharpDoubleAnti X) = (hsInner X (sharpDoubleAnti X)).re := by
  have h := sharpDoubleAnti_selfadjoint X (sharpDoubleAnti X)
  rw [sharpDoubleAnti_idempotent] at h
  rw [← h, zeroReserve_hsInner_self_re]

/-- On a symmetric matrix the two local swap pairings agree. -/
theorem sharpSwapRight_eq_left_of_symmetric (X : Matrix (L × R) (L × R) ℂ)
    (hX : Xᵀ = X) : sharpSwapRight X = sharpSwapLeft X := by
  ext i j
  exact (congrFun (congrFun hX (i.1, j.2)) (j.1, i.2)).symm

/-- Exact projection formula on the symmetric subspace. -/
theorem sharpDoubleAnti_symmetric_norm (X : Matrix (L × R) (L × R) ℂ)
    (hX : Xᵀ = X) :
    2 * frobSq (sharpDoubleAnti X) = frobSq X - (hsInner X (sharpSwapLeft X)).re := by
  have h := congrArg Complex.re (sharpDoubleAnti_pairing_right X X)
  rw [hX, sharpSwapRight_eq_left_of_symmetric X hX] at h
  norm_num [Complex.mul_re, zeroReserve_hsInner_self_re] at h
  rw [sharpDoubleAnti_frobSq]
  linarith

end Projection

section TwoRay

variable {L R : Type*} [Fintype L] [Fintype R]

/-- A symmetric rank-one term, with transpose and no conjugation. -/
def sharpSymmetricRay (z : L × R → ℂ) : Matrix (L × R) (L × R) ℂ :=
  fun i j => z i * z j

/-- The literal reshaping of a bipartite coefficient vector. -/
def sharpReshape (z : L × R → ℂ) : Matrix L R ℂ := fun i j => z (i, j)

/-- The cross-swap pairing is the square trace of the original cross Gram. -/
theorem sharpSymmetricRay_swap_pairing (z w : L × R → ℂ) :
    hsInner (sharpSymmetricRay z) (sharpSwapLeft (sharpSymmetricRay w)) =
      ((sharpReshape z)ᴴ * sharpReshape w * ((sharpReshape z)ᴴ * sharpReshape w)).trace := by
  unfold hsInner sharpSymmetricRay sharpSwapLeft
  simp only [Fintype.sum_prod_type]
  rw [sum_perm_lrlr]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, sharpReshape,
    Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro k _
  simp only [map_mul]
  simp only [starRingEnd_apply]
  ring

/-- The diagonal swap pairing retains the original Gram purity. -/
theorem sharpSymmetricRay_swap_self (z : L × R → ℂ) :
    (hsInner (sharpSymmetricRay z) (sharpSwapLeft (sharpSymmetricRay z))).re =
      frobSq ((sharpReshape z)ᴴ * sharpReshape z) := by
  rw [sharpSymmetricRay_swap_pairing]
  have h := ofReal_frobSq_eq_trace ((sharpReshape z)ᴴ * sharpReshape z)
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] at h
  exact (congrArg Complex.re h).symm

/-- Exact local-swap quadratic form for an arbitrary real two-ray combination. -/
theorem sharpSymmetricRay_mix_swap (z w : L × R → ℂ) (c d : ℝ) :
    (hsInner ((c : ℂ) • sharpSymmetricRay z + (d : ℂ) • sharpSymmetricRay w)
      (sharpSwapLeft ((c : ℂ) • sharpSymmetricRay z + (d : ℂ) • sharpSymmetricRay w))).re =
        c ^ 2 * frobSq ((sharpReshape z)ᴴ * sharpReshape z) +
        d ^ 2 * frobSq ((sharpReshape w)ᴴ * sharpReshape w) +
        2 * c * d * (((sharpReshape z)ᴴ * sharpReshape w *
          ((sharpReshape z)ᴴ * sharpReshape w)).trace).re := by
  have hcross : (hsInner (sharpSymmetricRay w)
      (sharpSwapLeft (sharpSymmetricRay z))).re =
        (hsInner (sharpSymmetricRay z) (sharpSwapLeft (sharpSymmetricRay w))).re := by
    rw [hsInner_re_comm, sharpSwapLeft_selfadjoint]
  have hexpand : hsInner ((c : ℂ) • sharpSymmetricRay z + (d : ℂ) • sharpSymmetricRay w)
      (sharpSwapLeft ((c : ℂ) • sharpSymmetricRay z + (d : ℂ) • sharpSymmetricRay w)) =
      (c : ℂ) ^ 2 * hsInner (sharpSymmetricRay z) (sharpSwapLeft (sharpSymmetricRay z)) +
      (d : ℂ) ^ 2 * hsInner (sharpSymmetricRay w) (sharpSwapLeft (sharpSymmetricRay w)) +
      (c : ℂ) * d * (hsInner (sharpSymmetricRay z) (sharpSwapLeft (sharpSymmetricRay w)) +
        hsInner (sharpSymmetricRay w) (sharpSwapLeft (sharpSymmetricRay z))) := by
    simp only [hsInner, sharpSwapLeft, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      map_add, map_mul, Complex.conj_ofReal, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hexpand]
  simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, pow_two,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, add_zero, sub_zero,
    sharpSymmetricRay_swap_self, hcross]
  rw [sharpSymmetricRay_swap_pairing]
  ring

/-- The symmetric two-ray projection estimate, with the sharp factor one-half.
No orthogonality or normalization of the rays is required. -/
theorem sharpDoubleAnti_symmetric_pair_bound (z w : L × R → ℂ) (c d : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) :
    frobSq (sharpDoubleAnti ((c : ℂ) • sharpSymmetricRay z + (d : ℂ) • sharpSymmetricRay w)) ≤
      frobSq ((c : ℂ) • sharpSymmetricRay z + (d : ℂ) • sharpSymmetricRay w) / 2 := by
  let X := (c : ℂ) • sharpSymmetricRay z + (d : ℂ) • sharpSymmetricRay w
  have hX : Xᵀ = X := by
    ext i j
    simp only [X, Matrix.transpose_apply, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, sharpSymmetricRay]
    ring
  have hnorm := sharpDoubleAnti_symmetric_norm X hX
  have hswap := sharpSymmetricRay_mix_swap z w c d
  have hbound := sharpPartialTrace_symmetric_pair_square_bound
    (sharpReshape z) (sharpReshape w) c d hc hd
  have hsquare := sq_nonneg
    (c * Real.sqrt (frobSq ((sharpReshape z)ᴴ * sharpReshape z)) -
      d * Real.sqrt (frobSq ((sharpReshape w)ᴴ * sharpReshape w)))
  change frobSq (sharpDoubleAnti X) ≤ frobSq X / 2
  change (hsInner X (sharpSwapLeft X)).re = _ at hswap
  linarith

end TwoRay

end ThreeCopyQutritWerner
