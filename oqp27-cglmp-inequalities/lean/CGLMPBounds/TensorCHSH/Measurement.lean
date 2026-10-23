module

public import CGLMPBounds.Defs.TensorMeasurement
public import CGLMPBounds.TensorCHSH.Truncation

@[expose] public section


/-!
# The common-input tensor CHSH behaviour: equation (F.5)

Supplement, Appendix F.2: for the measurements `A₀ = Z`, `A₁ = X`, `B₀ = (Z + X)/√2`,
`B₁ = (Z − X)/√2` on every pair of `Φ_2^{⊗m} = Φ_{2^m}`, with a common input and all bits reported,
"The behaviour is `T_m(a,b|x,y) = 2^{-m}(1-r)^{m-K_{xy}} r^{K_{xy}}`", `r = (2 - √2)/4`.

* `trace_reindex_mul`, `trace_tensorProjector_mul` : traces of reindexed and tensor products;
* `trace_qubitProjector_pair` : single-pair traces `(1-r)` and `r`;
* `tensorCHSHTable_eq` : (F.5), `tensorCHSHTable m = tensorTable m chshErrRate`.
-/

namespace CGLMPBounds.TensorCHSH

open Matrix

noncomputable section

/-! ### Traces of reindexed and tensor-product matrices -/

theorem trace_reindex_mul {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ) (A B : Matrix ι ι ℂ) :
    Matrix.trace (Matrix.reindex e e A * Matrix.reindex e e B) = Matrix.trace (A * B) := by
  rw [Matrix.reindex_apply, Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
  unfold Matrix.trace
  exact Fintype.sum_equiv e.symm _ _ (fun _ => rfl)

theorem trace_tensorProjector_mul (m t t' : ℕ) (a b : Fin m → Bool) :
    Matrix.trace (tensorProjector m t a * tensorProjector m t' b)
      = ∏ j, Matrix.trace (qubitProjector t (a j) * qubitProjector t' (b j)) := by
  have h1 : ∀ j, Matrix.trace (qubitProjector t (a j) * qubitProjector t' (b j))
      = ∑ z : Fin 2 × Fin 2,
          qubitProjector t (a j) z.1 z.2 * qubitProjector t' (b j) z.2 z.1 := by
    intro j
    rw [Fintype.sum_prod_type]
    rfl
  rw [Finset.prod_congr rfl (fun j _ => h1 j), Finset.prod_univ_sum, Fintype.piFinset_univ]
  unfold Matrix.trace
  simp only [Matrix.diag, Matrix.mul_apply, tensorProjector, Matrix.of_apply,
    ← Finset.prod_mul_distrib]
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Equiv.arrowProdEquivProdArrow _ _ _) _ _ (fun _ => rfl)).symm

/-! ### Single-pair traces -/

theorem trace_pauliZ : Matrix.trace pauliZ = 0 := by
  rw [pauliZ, Matrix.trace_fin_two_of]
  norm_num

theorem trace_pauliX : Matrix.trace pauliX = 0 := by
  rw [pauliX, Matrix.trace_fin_two_of]
  norm_num

theorem trace_pauliZ_mul_pauliZ : Matrix.trace (pauliZ * pauliZ) = 2 := by
  rw [pauliZ, Matrix.mul_fin_two, Matrix.trace_fin_two_of]
  norm_num

theorem trace_pauliX_mul_pauliX : Matrix.trace (pauliX * pauliX) = 2 := by
  rw [pauliX, Matrix.mul_fin_two, Matrix.trace_fin_two_of]
  norm_num

theorem trace_pauliZ_mul_pauliX : Matrix.trace (pauliZ * pauliX) = 0 := by
  rw [pauliZ, pauliX, Matrix.mul_fin_two, Matrix.trace_fin_two_of]
  norm_num

theorem trace_pauliX_mul_pauliZ : Matrix.trace (pauliX * pauliZ) = 0 := by
  rw [pauliZ, pauliX, Matrix.mul_fin_two, Matrix.trace_fin_two_of]
  norm_num

theorem trace_chshObservable : ∀ t : ℕ, Matrix.trace (chshObservable t) = 0
  | 0 => trace_pauliZ
  | 1 => by
    show Matrix.trace ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹ • (pauliZ + pauliX)) = 0
    rw [Matrix.trace_smul, Matrix.trace_add, trace_pauliZ, trace_pauliX, add_zero, smul_zero]
  | 2 => trace_pauliX
  | _ + 3 => by
    show Matrix.trace ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹ • (pauliZ - pauliX)) = 0
    rw [Matrix.trace_smul, Matrix.trace_sub, trace_pauliZ, trace_pauliX, sub_zero, smul_zero]

/-- `Tr(O_A O_B) = ±2/√2`, with the minus sign exactly in the context `(1,1)`. -/
theorem trace_chshObservable_mul :
    ∀ x y : Fin 2, Matrix.trace (chshObservable (2 * x.val) * chshObservable (1 + 2 * y.val))
      = (if x = 1 ∧ y = 1 then -1 else 1) * ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹ * 2) := by
  refine Fin.forall_fin_two.mpr ⟨Fin.forall_fin_two.mpr ⟨?_, ?_⟩, Fin.forall_fin_two.mpr ⟨?_, ?_⟩⟩
  · show Matrix.trace (pauliZ * ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹ • (pauliZ + pauliX))) = _
    rw [Matrix.mul_smul, Matrix.mul_add, Matrix.trace_smul, Matrix.trace_add,
      trace_pauliZ_mul_pauliZ, trace_pauliZ_mul_pauliX, if_neg (by decide), smul_eq_mul]
    ring
  · show Matrix.trace (pauliZ * ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹ • (pauliZ - pauliX))) = _
    rw [Matrix.mul_smul, Matrix.mul_sub, Matrix.trace_smul, Matrix.trace_sub,
      trace_pauliZ_mul_pauliZ, trace_pauliZ_mul_pauliX, if_neg (by decide), smul_eq_mul]
    ring
  · show Matrix.trace (pauliX * ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹ • (pauliZ + pauliX))) = _
    rw [Matrix.mul_smul, Matrix.mul_add, Matrix.trace_smul, Matrix.trace_add,
      trace_pauliX_mul_pauliZ, trace_pauliX_mul_pauliX, if_neg (by decide), smul_eq_mul]
    ring
  · show Matrix.trace (pauliX * ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹ • (pauliZ - pauliX))) = _
    rw [Matrix.mul_smul, Matrix.mul_sub, Matrix.trace_smul, Matrix.trace_sub,
      trace_pauliX_mul_pauliZ, trace_pauliX_mul_pauliX, if_pos (by decide), smul_eq_mul]
    ring

/-- `Tr(P_c(O) P_{c'}(O')) = (2 + (-1)^{c+c'} Tr(O O'))/4` for traceless `O`, `O'`. -/
theorem trace_qubitProjector_mul (t t' : ℕ) (c c' : Bool)
    (hO : Matrix.trace (chshObservable t) = 0) (hO' : Matrix.trace (chshObservable t') = 0) :
    Matrix.trace (qubitProjector t c * qubitProjector t' c')
      = (1 / 4 : ℂ) * (2 + (if c then (-1 : ℂ) else 1) * (if c' then (-1 : ℂ) else 1)
          * Matrix.trace (chshObservable t * chshObservable t')) := by
  unfold qubitProjector
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul,
    Matrix.mul_one, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, hO,
    hO', smul_eq_mul, mul_zero, add_zero]
  push_cast
  ring

/-- Single-pair factor of (F.5): `Tr(P^{2x}_c P^{1+2y}_{c'}) = (1-r)^{1-e} r^e`, where `e` is the
CHSH error indicator of the pair. -/
theorem trace_qubitProjector_pair (x y : Fin 2) (c c' : Bool) :
    Matrix.trace (qubitProjector (2 * x.val) c * qubitProjector (1 + 2 * y.val) c')
      = (((1 - chshErrRate) ^ (1 - errBit x y c c') * chshErrRate ^ errBit x y c c' : ℝ) : ℂ) := by
  have hs0 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    exact_mod_cast this.ne'
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hinv : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * 2 = ((Real.sqrt 2 : ℝ) : ℂ) := by
    rw [← hs, ← mul_assoc, inv_mul_cancel₀ hs0, one_mul]
  rw [trace_qubitProjector_mul _ _ c c' (trace_chshObservable _) (trace_chshObservable _),
    trace_chshObservable_mul, hinv]
  unfold errBit chshErrRate
  push_cast
  revert x y
  refine Fin.forall_fin_two.mpr ⟨Fin.forall_fin_two.mpr ⟨?_, ?_⟩, Fin.forall_fin_two.mpr ⟨?_, ?_⟩⟩ <;>
    cases c <;> cases c' <;> simp <;> ring

/-! ### Equation (F.5) -/

/-- **Equation (F.5).** The common-input tensor CHSH behaviour on `Φ_{2^m}` is
`T_m(a,b|x,y) = 2^{-m} (1-r)^{m-K_{xy}} r^{K_{xy}}` with `r = (2 - √2)/4`. -/
theorem tensorCHSHTable_eq (m : ℕ) : tensorCHSHTable m = tensorTable m chshErrRate := by
  funext x y a b
  show (Matrix.trace (tensorProjectorFin m (2 * x.val) a
      * tensorProjectorFin m (1 + 2 * y.val) b)).re / ((2 ^ m : ℕ) : ℝ) = _
  rw [tensorProjectorFin, tensorProjectorFin, trace_reindex_mul, trace_tensorProjector_mul]
  simp only [trace_qubitProjector_pair]
  rw [← Complex.ofReal_prod, Complex.ofReal_re, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum]
  have hK : ∑ j, errBit x y (a j) (b j) = errCount x y a b := (errCount_eq_sum x y a b).symm
  have hK' : ∑ j : Fin m, (1 - errBit x y (a j) (b j)) = m - errCount x y a b := by
    have hsum : ∑ j : Fin m, (1 - errBit x y (a j) (b j))
        + ∑ j : Fin m, errBit x y (a j) (b j) = m := by
      rw [← Finset.sum_add_distrib,
        Finset.sum_congr rfl (fun j _ => Nat.sub_add_cancel (errBit_le_one x y (a j) (b j)))]
      simp
    rw [← hK]
    omega
  rw [hK, hK']
  unfold tensorTable
  rw [div_eq_mul_one_div, Nat.cast_pow, Nat.cast_ofNat, _root_.one_div_pow]
  ring

end

end CGLMPBounds.TensorCHSH
