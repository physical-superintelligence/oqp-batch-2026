module

public import ThreeCopyQutritWerner.CertificateX2BridgeImages
public import ThreeCopyQutritWerner.CertificateX2BridgeParity

@[expose] public section


/-!
# The S3 group algebra on a frame index with three equal sites

On `Fin (m * (m * m))` (three sites with the same multiplicity `m`) the six site permutations act
by function matrices `x2S3Mat m q` (`q : Fin 6`, the order of `x2Perm3`), with
`x2S3Mat m q * x2S3Mat m r = x2S3Mat m (x2Perm3Mul q r)`. The averages
`x2S3Avg m = (1/6) Σ_q P_q` and `x2S3Alt m = (1/6) Σ_q sign q • P_q` absorb permutations
(`P_r * avg = avg * P_r = avg`, `alt * P_r = P_r * alt = sign r • alt`); hence `avg`, `alt` and
`std = 1 - avg - alt` are orthogonal idempotents, and splitting `std` by the swap of the first two
sites gives the four parts of a triple of three equal types (`x2S3Part`).
-/

noncomputable section

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

/-! ## Function matrices -/

/-- The 0/1 matrix of a map: entry `(i, j)` is `1` iff `f i = j`. -/
def x2FunMat {n : Type*} [DecidableEq n] (f : n → n) : Matrix n n ℂ :=
  Matrix.of fun i j => if f i = j then 1 else 0

theorem x2FunMat_mul_apply {n : Type*} [Fintype n] [DecidableEq n] (f : n → n)
    (M : Matrix n n ℂ) (i j : n) : (x2FunMat f * M) i j = M (f i) j := by
  simp only [x2FunMat, Matrix.mul_apply, Matrix.of_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem x2FunMat_mul {n : Type*} [Fintype n] [DecidableEq n] (f g : n → n) :
    x2FunMat f * x2FunMat g = x2FunMat (g ∘ f) := by
  ext i j
  rw [x2FunMat_mul_apply]
  rfl

theorem x2FunMat_apply_mul {n : Type*} [Fintype n] [DecidableEq n] (f g : n → n)
    (hfg : ∀ x, f (g x) = x) (hgf : ∀ x, g (f x) = x) (M : Matrix n n ℂ) (i j : n) :
    (M * x2FunMat f) i j = M i (g j) := by
  simp only [x2FunMat, Matrix.mul_apply, Matrix.of_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (g j)]
  · rw [if_pos (hfg j)]
  · intro l _ hl
    rw [if_neg]
    intro h
    apply hl
    rw [← h, hgf]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem x2FunMat_comm {n : Type*} [Fintype n] [DecidableEq n] (f g : n → n)
    (hfg : ∀ x, f (g x) = x) (hgf : ∀ x, g (f x) = x) (M : Matrix n n ℂ)
    (hM : ∀ i j, M (f i) (f j) = M i j) : M * x2FunMat f = x2FunMat f * M := by
  ext i j
  rw [x2FunMat_mul_apply, x2FunMat_apply_mul f g hfg hgf, ← hM i (g j), hfg]

theorem x2FunMat_conjTranspose {n : Type*} [DecidableEq n] (f g : n → n)
    (hfg : ∀ x, f (g x) = x) (hgf : ∀ x, g (f x) = x) : (x2FunMat f)ᴴ = x2FunMat g := by
  ext i j
  simp only [x2FunMat, Matrix.conjTranspose_apply, Matrix.of_apply]
  by_cases h : g i = j
  · rw [if_pos h, if_pos (by rw [← h, hfg]), star_one]
  · rw [if_neg h, if_neg (fun h' => h (by rw [← h', hgf])), star_zero]

theorem x2FunMat_id {n : Type*} [DecidableEq n] : x2FunMat (fun x : n => x) = 1 := by
  ext i j
  simp only [x2FunMat, Matrix.of_apply, Matrix.one_apply]

/-! ## Site permutations on three equal sites -/

/-- Coordinates of a frame index with three equal sites. -/
def x2Coords3 (m : ℕ) (i : Fin (m * (m * m))) : Fin 3 → Fin m :=
  ![(finProdFinEquiv.symm i).1, (finProdFinEquiv.symm (finProdFinEquiv.symm i).2).1,
    (finProdFinEquiv.symm (finProdFinEquiv.symm i).2).2]

/-- The frame index of coordinates. -/
def x2Idx3 (m : ℕ) (v : Fin 3 → Fin m) : Fin (m * (m * m)) :=
  finProdFinEquiv (v 0, finProdFinEquiv (v 1, v 2))

theorem x2Coords3_idx (m : ℕ) (v : Fin 3 → Fin m) : x2Coords3 m (x2Idx3 m v) = v := by
  funext k
  fin_cases k <;> simp [x2Coords3, x2Idx3]

theorem x2Idx3_coords (m : ℕ) (i : Fin (m * (m * m))) : x2Idx3 m (x2Coords3 m i) = i := by
  show finProdFinEquiv ((finProdFinEquiv.symm i).1,
    finProdFinEquiv ((finProdFinEquiv.symm (finProdFinEquiv.symm i).2).1,
      (finProdFinEquiv.symm (finProdFinEquiv.symm i).2).2)) = i
  simp only [Prod.mk.eta, Equiv.apply_symm_apply]

/-- The site permutation `q` on frame indices: `(P_q v)(x) = v(x ∘ x2Perm3 q)`. -/
def x2SlotMap3 (m : ℕ) (q : Fin 6) (i : Fin (m * (m * m))) : Fin (m * (m * m)) :=
  x2Idx3 m (x2Coords3 m i ∘ x2Perm3 q)

theorem x2SlotMap3_comp (m : ℕ) (q r : Fin 6) (i : Fin (m * (m * m))) :
    x2SlotMap3 m r (x2SlotMap3 m q i) = x2SlotMap3 m (x2Perm3Mul q r) i := by
  simp only [x2SlotMap3, x2Coords3_idx, x2_perm3Mul_spec, Function.comp_assoc]

/-- Inverses in `x2Perm3` order. -/
def x2Perm3Inv : Fin 6 → Fin 6 := ![0, 1, 2, 4, 3, 5]

theorem x2_perm3Inv_spec : ∀ q : Fin 6,
    x2Perm3Mul q (x2Perm3Inv q) = 0 ∧ x2Perm3Mul (x2Perm3Inv q) q = 0 := by
  decide +kernel

theorem x2SlotMap3_zero (m : ℕ) (i : Fin (m * (m * m))) : x2SlotMap3 m 0 i = i := by
  have h : x2Coords3 m i ∘ x2Perm3 0 = x2Coords3 m i := by
    funext k
    fin_cases k <;> rfl
  rw [x2SlotMap3, h, x2Idx3_coords]

theorem x2SlotMap3_inv_left (m : ℕ) (q : Fin 6) (i : Fin (m * (m * m))) :
    x2SlotMap3 m q (x2SlotMap3 m (x2Perm3Inv q) i) = i := by
  rw [x2SlotMap3_comp, (x2_perm3Inv_spec q).2, x2SlotMap3_zero]

theorem x2SlotMap3_inv_right (m : ℕ) (q : Fin 6) (i : Fin (m * (m * m))) :
    x2SlotMap3 m (x2Perm3Inv q) (x2SlotMap3 m q i) = i := by
  rw [x2SlotMap3_comp, (x2_perm3Inv_spec q).1, x2SlotMap3_zero]

/-- The permutation matrices. -/
def x2S3Mat (m : ℕ) (q : Fin 6) : Matrix (Fin (m * (m * m))) (Fin (m * (m * m))) ℂ :=
  x2FunMat (x2SlotMap3 m q)

theorem x2S3Mat_mul (m : ℕ) (q r : Fin 6) :
    x2S3Mat m q * x2S3Mat m r = x2S3Mat m (x2Perm3Mul q r) := by
  unfold x2S3Mat
  rw [x2FunMat_mul]
  congr 1
  funext i
  exact x2SlotMap3_comp m q r i

theorem x2S3Mat_conjTranspose (m : ℕ) (q : Fin 6) :
    (x2S3Mat m q)ᴴ = x2S3Mat m (x2Perm3Inv q) :=
  x2FunMat_conjTranspose _ _ (x2SlotMap3_inv_left m q) (x2SlotMap3_inv_right m q)

theorem x2S3Mat_comm (m : ℕ) (q : Fin 6) (M : Matrix (Fin (m * (m * m))) (Fin (m * (m * m))) ℂ)
    (hM : ∀ i j, M (x2SlotMap3 m q i) (x2SlotMap3 m q j) = M i j) :
    M * x2S3Mat m q = x2S3Mat m q * M :=
  x2FunMat_comm _ _ (x2SlotMap3_inv_left m q) (x2SlotMap3_inv_right m q) M hM

/-! ## The group algebra -/

/-- Signs in `x2Perm3` order, as complex numbers. -/
def x2S3Sign (q : Fin 6) : ℂ := ((x2Perm3Sign q : ℚ) : ℂ)

theorem x2_perm3Sign_mul : ∀ q r : Fin 6,
    x2Perm3Sign (x2Perm3Mul q r) = x2Perm3Sign q * x2Perm3Sign r := by
  intro q r
  fin_cases q <;> fin_cases r <;> simp [x2Perm3Sign, x2Perm3Mul]

theorem x2_perm3Sign_sq : ∀ q : Fin 6, x2Perm3Sign q * x2Perm3Sign q = 1 := by
  intro q
  fin_cases q <;> simp [x2Perm3Sign]

theorem x2_perm3Mul_bijective_left : ∀ r : Fin 6, Function.Bijective (fun q => x2Perm3Mul q r) := by
  decide +kernel

theorem x2S3Sign_mul (q r : Fin 6) : x2S3Sign (x2Perm3Mul q r) = x2S3Sign q * x2S3Sign r := by
  unfold x2S3Sign
  rw [x2_perm3Sign_mul]
  push_cast
  ring

theorem x2S3Sign_sq (q : Fin 6) : x2S3Sign q * x2S3Sign q = 1 := by
  unfold x2S3Sign
  rw [← Rat.cast_mul, x2_perm3Sign_sq, Rat.cast_one]

theorem x2S3Sign_sum : ∑ q : Fin 6, x2S3Sign q = 0 := by
  rw [Fin.sum_univ_six]
  norm_num [x2S3Sign, x2Perm3Sign]

theorem x2S3Sign_inv (q : Fin 6) : x2S3Sign (x2Perm3Inv q) = x2S3Sign q := by
  fin_cases q <;> rfl

theorem x2_perm3Inv_bijective : Function.Bijective x2Perm3Inv := by
  decide +kernel

theorem x2S3Sign_star (q : Fin 6) : star (x2S3Sign q) = x2S3Sign q := by
  fin_cases q <;> simp [x2S3Sign, x2Perm3Sign]

/-- The trivial-isotypic projector. -/
def x2S3Avg (m : ℕ) : Matrix (Fin (m * (m * m))) (Fin (m * (m * m))) ℂ :=
  (1 / 6 : ℂ) • ∑ q, x2S3Mat m q

/-- The sign-isotypic projector. -/
def x2S3Alt (m : ℕ) : Matrix (Fin (m * (m * m))) (Fin (m * (m * m))) ℂ :=
  (1 / 6 : ℂ) • ∑ q, x2S3Sign q • x2S3Mat m q

theorem x2S3Avg_mul_mat (m : ℕ) (r : Fin 6) : x2S3Avg m * x2S3Mat m r = x2S3Avg m := by
  unfold x2S3Avg
  rw [Matrix.smul_mul, Finset.sum_mul]
  simp only [x2S3Mat_mul]
  congr 1
  exact Fintype.sum_bijective _ (x2_perm3Mul_bijective_left r) _ _ (fun _ => rfl)

theorem x2S3Mat_mul_avg (m : ℕ) (r : Fin 6) : x2S3Mat m r * x2S3Avg m = x2S3Avg m := by
  unfold x2S3Avg
  rw [Matrix.mul_smul, Finset.mul_sum]
  simp only [x2S3Mat_mul]
  congr 1
  exact Fintype.sum_bijective _ (x2_perm3Mul_bijective r) _ _ (fun _ => rfl)

theorem x2S3Alt_mul_mat (m : ℕ) (r : Fin 6) :
    x2S3Alt m * x2S3Mat m r = x2S3Sign r • x2S3Alt m := by
  have h1 : x2S3Alt m * x2S3Mat m r =
      (1 / 6 : ℂ) • ∑ q, (x2S3Sign q • x2S3Mat m q) * x2S3Mat m r := by
    rw [← Finset.sum_mul, ← Matrix.smul_mul]
    rfl
  have h2 : x2S3Sign r • x2S3Alt m =
      (1 / 6 : ℂ) • ∑ q, x2S3Sign r • (x2S3Sign q • x2S3Mat m q) := by
    rw [← Finset.smul_sum, smul_comm (1 / 6 : ℂ) (x2S3Sign r) (∑ q, x2S3Sign q • x2S3Mat m q)]
    rfl
  rw [h1, h2]
  congr 1
  refine Fintype.sum_bijective (fun q => x2Perm3Mul q r) (x2_perm3Mul_bijective_left r)
    (fun q => (x2S3Sign q • x2S3Mat m q) * x2S3Mat m r)
    (fun q => x2S3Sign r • (x2S3Sign q • x2S3Mat m q)) (fun q => ?_)
  have hs : x2S3Sign r * (x2S3Sign q * x2S3Sign r) = x2S3Sign q := by
    rw [mul_comm (x2S3Sign q), ← mul_assoc, x2S3Sign_sq, one_mul]
  rw [Matrix.smul_mul, x2S3Mat_mul, smul_smul, x2S3Sign_mul, hs]

theorem x2S3Mat_mul_alt (m : ℕ) (r : Fin 6) :
    x2S3Mat m r * x2S3Alt m = x2S3Sign r • x2S3Alt m := by
  have h1 : x2S3Mat m r * x2S3Alt m =
      (1 / 6 : ℂ) • ∑ q, x2S3Mat m r * (x2S3Sign q • x2S3Mat m q) := by
    rw [← Finset.mul_sum, ← Matrix.mul_smul]
    rfl
  have h2 : x2S3Sign r • x2S3Alt m =
      (1 / 6 : ℂ) • ∑ q, x2S3Sign r • (x2S3Sign q • x2S3Mat m q) := by
    rw [← Finset.smul_sum, smul_comm (1 / 6 : ℂ) (x2S3Sign r) (∑ q, x2S3Sign q • x2S3Mat m q)]
    rfl
  rw [h1, h2]
  congr 1
  refine Fintype.sum_bijective (x2Perm3Mul r) (x2_perm3Mul_bijective r)
    (fun q => x2S3Mat m r * (x2S3Sign q • x2S3Mat m q))
    (fun q => x2S3Sign r • (x2S3Sign q • x2S3Mat m q)) (fun q => ?_)
  have hs : x2S3Sign r * (x2S3Sign r * x2S3Sign q) = x2S3Sign q := by
    rw [← mul_assoc, x2S3Sign_sq, one_mul]
  rw [Matrix.mul_smul, x2S3Mat_mul, smul_smul, x2S3Sign_mul, hs]

theorem x2S3Avg_idem (m : ℕ) : x2S3Avg m * x2S3Avg m = x2S3Avg m := by
  have h : x2S3Avg m * x2S3Avg m = (1 / 6 : ℂ) • ∑ q, x2S3Avg m * x2S3Mat m q := by
    rw [← Finset.mul_sum, ← Matrix.mul_smul]
    rfl
  rw [h]
  simp only [x2S3Avg_mul_mat, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  norm_num

theorem x2S3Alt_idem (m : ℕ) : x2S3Alt m * x2S3Alt m = x2S3Alt m := by
  have h : x2S3Alt m * x2S3Alt m =
      (1 / 6 : ℂ) • ∑ q, x2S3Alt m * (x2S3Sign q • x2S3Mat m q) := by
    rw [← Finset.mul_sum, ← Matrix.mul_smul]
    rfl
  rw [h]
  simp only [Matrix.mul_smul, x2S3Alt_mul_mat, smul_smul, x2S3Sign_sq, one_smul,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  norm_num

theorem x2S3Avg_mul_alt (m : ℕ) : x2S3Avg m * x2S3Alt m = 0 := by
  have h : x2S3Avg m * x2S3Alt m =
      (1 / 6 : ℂ) • ∑ q, x2S3Avg m * (x2S3Sign q • x2S3Mat m q) := by
    rw [← Finset.mul_sum, ← Matrix.mul_smul]
    rfl
  rw [h]
  simp only [Matrix.mul_smul, x2S3Avg_mul_mat]
  rw [← Finset.sum_smul, x2S3Sign_sum, zero_smul, smul_zero]

theorem x2S3Alt_mul_avg (m : ℕ) : x2S3Alt m * x2S3Avg m = 0 := by
  have h : x2S3Alt m * x2S3Avg m = (1 / 6 : ℂ) • ∑ q, x2S3Alt m * x2S3Mat m q := by
    rw [← Finset.mul_sum, ← Matrix.mul_smul]
    rfl
  rw [h]
  simp only [x2S3Alt_mul_mat]
  rw [← Finset.sum_smul, x2S3Sign_sum, zero_smul, smul_zero]

theorem x2S3Avg_conjTranspose (m : ℕ) : (x2S3Avg m)ᴴ = x2S3Avg m := by
  unfold x2S3Avg
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sum]
  simp only [x2S3Mat_conjTranspose]
  congr 1
  · simp
  · exact Fintype.sum_bijective _ x2_perm3Inv_bijective _ _ (fun _ => rfl)

theorem x2S3Alt_conjTranspose (m : ℕ) : (x2S3Alt m)ᴴ = x2S3Alt m := by
  unfold x2S3Alt
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sum]
  simp only [Matrix.conjTranspose_smul, x2S3Mat_conjTranspose, x2S3Sign_star]
  congr 1
  · simp
  · refine Fintype.sum_bijective _ x2_perm3Inv_bijective _ _ (fun q => ?_)
    rw [x2S3Sign_inv]

end ThreeCopyQutritWerner

end
