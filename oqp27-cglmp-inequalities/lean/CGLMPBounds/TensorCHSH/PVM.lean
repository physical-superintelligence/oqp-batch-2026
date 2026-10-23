module

public import CGLMPBounds.TensorCHSH.Measurement
public import CGLMPBounds.Quantum.Tracial

@[expose] public section


/-!
# The common-input tensor CHSH measurements are projective

Supplement, Appendix F.2: the measurements of `T_m` are the common-setting tensor products of the
single-pair eigenprojectors of `Z`, `X`, `(Z ± X)/√2`. This file proves that, for every setting
`t`, the `2^m` operators `tensorProjectorFin m t a` form a projective measurement on `ℂ^{2^m}`, so
`T_m = tensorCHSHTable m` is a genuine tracial quantum behaviour (and hence no-signalling).

* `chshObservable_mul_self`, `chshObservable_isHermitian` : each single-pair observable is a
  Hermitian involution;
* `qubitProjector_mul_self`, `sum_qubitProjector`, `qubitProjector_conjTranspose`;
* `tensorProjector_mul_self`, `sum_tensorProjector`, `tensorProjector_conjTranspose`;
* `tensorProjectorFin_isPVM`, `tensorCHSHTable_isNoSignalling`.
-/

namespace CGLMPBounds.TensorCHSH

open Matrix

noncomputable section

theorem pauliZ_mul_self : pauliZ * pauliZ = 1 := by
  rw [pauliZ, Matrix.mul_fin_two, Matrix.one_fin_two]
  norm_num

theorem pauliX_mul_self : pauliX * pauliX = 1 := by
  rw [pauliX, Matrix.mul_fin_two, Matrix.one_fin_two]
  norm_num

theorem pauliZ_mul_pauliX_add : pauliZ * pauliX + pauliX * pauliZ = 0 := by
  rw [pauliZ, pauliX, Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem pauliZ_isHermitian : pauliZ.IsHermitian := by
  show pauliZᴴ = pauliZ
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliZ]

theorem pauliX_isHermitian : pauliX.IsHermitian := by
  show pauliXᴴ = pauliX
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliX]

theorem sqrt_two_inv_mul_self :
    (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ * (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ * 2 = 1 := by
  have hs0 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    exact_mod_cast this.ne'
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [← hs, mul_mul_mul_comm, inv_mul_cancel₀ hs0, one_mul]

/-- Each single-pair observable squares to the identity. -/
theorem chshObservable_mul_self : ∀ t : ℕ, chshObservable t * chshObservable t = 1
  | 0 => pauliZ_mul_self
  | 1 => by
    show ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹ • (pauliZ + pauliX))
      * ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹ • (pauliZ + pauliX)) = 1
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, add_mul, mul_add, mul_add, pauliZ_mul_self,
      pauliX_mul_self]
    have e : (1 : Matrix (Fin 2) (Fin 2) ℂ) + pauliZ * pauliX + (pauliX * pauliZ + 1)
        = (2 : ℂ) • 1 := by
      rw [show (1 : Matrix (Fin 2) (Fin 2) ℂ) + pauliZ * pauliX + (pauliX * pauliZ + 1)
          = (pauliZ * pauliX + pauliX * pauliZ) + (1 + 1) by abel, pauliZ_mul_pauliX_add,
        zero_add, two_smul]
    rw [e, smul_smul, sqrt_two_inv_mul_self, one_smul]
  | 2 => pauliX_mul_self
  | _ + 3 => by
    show ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹ • (pauliZ - pauliX))
      * ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹ • (pauliZ - pauliX)) = 1
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, sub_mul, mul_sub, mul_sub, pauliZ_mul_self,
      pauliX_mul_self]
    have e : (1 : Matrix (Fin 2) (Fin 2) ℂ) - pauliZ * pauliX - (pauliX * pauliZ - 1)
        = (2 : ℂ) • 1 := by
      rw [show (1 : Matrix (Fin 2) (Fin 2) ℂ) - pauliZ * pauliX - (pauliX * pauliZ - 1)
          = (1 + 1) - (pauliZ * pauliX + pauliX * pauliZ) by abel, pauliZ_mul_pauliX_add,
        sub_zero, two_smul]
    rw [e, smul_smul, sqrt_two_inv_mul_self, one_smul]

theorem star_sqrt_two_inv : star (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ = (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ := by
  rw [← Complex.ofReal_inv]
  exact Complex.conj_ofReal _

/-- Each single-pair observable is Hermitian. -/
theorem chshObservable_isHermitian : ∀ t : ℕ, (chshObservable t).IsHermitian
  | 0 => pauliZ_isHermitian
  | 1 => by
    show ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹ • (pauliZ + pauliX))ᴴ
      = (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ • (pauliZ + pauliX)
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, pauliZ_isHermitian.eq,
      pauliX_isHermitian.eq, star_sqrt_two_inv]
  | 2 => pauliX_isHermitian
  | _ + 3 => by
    show ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹ • (pauliZ - pauliX))ᴴ
      = (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ • (pauliZ - pauliX)
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, pauliZ_isHermitian.eq,
      pauliX_isHermitian.eq, star_sqrt_two_inv]

theorem qubitProjector_mul_self (t : ℕ) (c : Bool) :
    qubitProjector t c * qubitProjector t c = qubitProjector t c := by
  have hs : (if c then (-1 : ℂ) else 1) * (if c then (-1 : ℂ) else 1) = 1 := by
    cases c <;> norm_num
  have hA : ((if c then (-1 : ℂ) else 1) • chshObservable t)
      * ((if c then (-1 : ℂ) else 1) • chshObservable t) = 1 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hs, chshObservable_mul_self, one_smul]
  have key : (1 + (if c then (-1 : ℂ) else 1) • chshObservable t)
      * (1 + (if c then (-1 : ℂ) else 1) • chshObservable t)
      = (2 : ℂ) • (1 + (if c then (-1 : ℂ) else 1) • chshObservable t) := by
    simp only [add_mul, mul_add, one_mul, mul_one, hA]
    rw [two_smul]
    abel
  unfold qubitProjector
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, key, smul_smul]
  norm_num

theorem sum_qubitProjector (t : ℕ) : ∑ c : Bool, qubitProjector t c = 1 := by
  rw [Fintype.sum_bool]
  show (1 / 2 : ℂ) • (1 + (-1 : ℂ) • chshObservable t)
    + (1 / 2 : ℂ) • (1 + (1 : ℂ) • chshObservable t) = 1
  rw [neg_one_smul, one_smul, ← smul_add,
    show (1 : Matrix (Fin 2) (Fin 2) ℂ) + -chshObservable t + (1 + chshObservable t)
      = (2 : ℂ) • 1 by rw [two_smul]; abel, smul_smul]
  norm_num

theorem qubitProjector_conjTranspose (t : ℕ) (c : Bool) :
    (qubitProjector t c)ᴴ = qubitProjector t c := by
  unfold qubitProjector
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_one,
    Matrix.conjTranspose_smul, (chshObservable_isHermitian t).eq]
  cases c <;> simp

theorem prod_sum_fin {m : ℕ} {κ : Type*} [Fintype κ] (F : Fin m → κ → ℂ) :
    ∏ j, ∑ c, F j c = ∑ x : Fin m → κ, ∏ j, F j (x j) := by
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

theorem tensorProjector_conjTranspose (m t : ℕ) (a : Fin m → Bool) :
    (tensorProjector m t a)ᴴ = tensorProjector m t a := by
  ext s s'
  rw [Matrix.conjTranspose_apply]
  simp only [tensorProjector, Matrix.of_apply]
  rw [star_prod]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  have h := congrFun (congrFun (qubitProjector_conjTranspose t (a j)) (s j)) (s' j)
  rw [Matrix.conjTranspose_apply] at h
  exact h

theorem tensorProjector_mul_self (m t : ℕ) (a : Fin m → Bool) :
    tensorProjector m t a * tensorProjector m t a = tensorProjector m t a := by
  ext s s''
  rw [Matrix.mul_apply]
  simp only [tensorProjector, Matrix.of_apply, ← Finset.prod_mul_distrib]
  rw [← prod_sum_fin (fun j c => qubitProjector t (a j) (s j) c * qubitProjector t (a j) c (s'' j))]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  show ∑ c, qubitProjector t (a j) (s j) c * qubitProjector t (a j) c (s'' j) = _
  rw [← Matrix.mul_apply, qubitProjector_mul_self]

theorem sum_tensorProjector (m t : ℕ) : ∑ a, tensorProjector m t a = 1 := by
  ext s s'
  rw [Matrix.sum_apply]
  simp only [tensorProjector, Matrix.of_apply]
  rw [← prod_sum_fin (fun j c => qubitProjector t c (s j) (s' j))]
  have h1 : ∀ j, ∑ c : Bool, qubitProjector t c (s j) (s' j)
      = (1 : Matrix (Fin 2) (Fin 2) ℂ) (s j) (s' j) := fun j => by
    rw [← Matrix.sum_apply, sum_qubitProjector]
  simp only [h1]
  by_cases h : s = s'
  · subst h
    rw [Matrix.one_apply_eq]
    exact Finset.prod_eq_one (fun j _ => Matrix.one_apply_eq _)
  · rw [Matrix.one_apply_ne h]
    obtain ⟨j, hj⟩ : ∃ j, s j ≠ s' j := by
      by_contra hcon
      push_neg at hcon
      exact h (funext hcon)
    exact Finset.prod_eq_zero (Finset.mem_univ j) (Matrix.one_apply_ne hj)

/-- For every setting `t`, the tensor CHSH projectors on `ℂ^{2^m}` form a projective
measurement. -/
theorem tensorProjectorFin_isPVM (m t : ℕ) : IsPVM (tensorProjectorFin m t) where
  isHermitian a := by
    show (tensorProjectorFin m t a)ᴴ = tensorProjectorFin m t a
    unfold tensorProjectorFin
    rw [Matrix.conjTranspose_reindex, tensorProjector_conjTranspose]
  mul_self a := by
    unfold tensorProjectorFin
    rw [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, tensorProjector_mul_self]
  sum_eq_one := by
    ext i j
    simp only [tensorProjectorFin, Matrix.sum_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
    rw [← Matrix.sum_apply, sum_tensorProjector, Matrix.one_apply, Matrix.one_apply]
    simp only [Equiv.apply_eq_iff_eq]

/-- `T_m` is a tracial quantum behaviour of projective measurements, hence no-signalling. -/
theorem tensorCHSHTable_isNoSignalling (m : ℕ) : IsNoSignalling (tensorCHSHTable m) :=
  tracialTable_isNoSignalling (fun _ => tensorProjectorFin_isPVM m _)
    (fun _ => tensorProjectorFin_isPVM m _)

end

end CGLMPBounds.TensorCHSH
