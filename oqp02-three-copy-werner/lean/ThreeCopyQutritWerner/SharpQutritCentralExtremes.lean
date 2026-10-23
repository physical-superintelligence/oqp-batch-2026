module

public import ThreeCopyQutritWerner.SharpQutritCentralOrder
public import Mathlib.Analysis.Matrix.PosDef

@[expose] public section


/-!
# Central spectral extremes dominate the external qutrit blocks

The actual spectral theorem supplies positive affine shifts of the central
matrix. Literal two-coordinate test vectors then bound every exterior
coefficient by both central extremes; no interlacing premise is supplied.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace ThreeCopyQutritWerner

/-- A real affine function nonnegative on every actual Hermitian eigenvalue
gives a positive semidefinite affine function of the original matrix. -/
theorem hermitian_affine_posSemidef_of_eigenvalues
    {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (a b : ℝ)
    (h : ∀ i, 0 ≤ a * hH.eigenvalues i + b) :
    ((a : ℂ) • H + (b : ℂ) • (1 : Matrix n n ℂ)).PosSemidef := by
  let U : Matrix n n ℂ := hH.eigenvectorUnitary
  let D : Matrix n n ℂ := Matrix.diagonal (fun i => (hH.eigenvalues i : ℂ))
  have hUU : U * Uᴴ = 1 := Unitary.coe_mul_star_self hH.eigenvectorUnitary
  have hfac : H = U * D * Uᴴ := by
    simpa only [Unitary.conjStarAlgAut_apply, U, D, Function.comp_apply,
      RCLike.ofReal_eq_complex_ofReal, Matrix.star_eq_conjTranspose]
      using! hH.spectral_theorem
  have hp : (Matrix.diagonal (fun i => ((a * hH.eigenvalues i + b : ℝ) : ℂ))).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    change (0 : ℂ) ≤ ((a * hH.eigenvalues i + b : ℝ) : ℂ)
    exact Complex.zero_le_real.mpr (h i)
  have hdiag : Matrix.diagonal (fun i => ((a * hH.eigenvalues i + b : ℝ) : ℂ)) =
      (a : ℂ) • D + (b : ℂ) • (1 : Matrix n n ℂ) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [D, Matrix.diagonal_apply, Matrix.smul_apply, Complex.ofReal_add,
        Complex.ofReal_mul]
    · simp [D, Matrix.diagonal_apply, Matrix.one_apply, Matrix.smul_apply, hij]
  have hpU := hp.mul_mul_conjTranspose_same U
  rw [hdiag] at hpU
  have heq : U * ((a : ℂ) • D + (b : ℂ) • (1 : Matrix n n ℂ)) * Uᴴ =
      (a : ℂ) • H + (b : ℂ) • (1 : Matrix n n ℂ) := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one]
    rw [← hfac, hUU]
  rw [heq] at hpU
  exact hpU

/-- The ordered endpoints bound every member of the actual original
Hermitian eigenvalue family through its exact permutation. -/
theorem sharpQutritCentralEigenvalue_between_extremes (d : Fin 3 → ℝ) (j : Fin 3) :
    sharpQutritCentralOrdered d 2 ≤ sharpQutritCentralEigenvalue d j ∧
      sharpQutritCentralEigenvalue d j ≤ sharpQutritCentralOrdered d 0 := by
  obtain ⟨e, he⟩ := sharpQutritCentralOrdered_reindex d
  have hj : sharpQutritCentralEigenvalue d j = sharpQutritCentralOrdered d (e.symm j) := by
    simpa only [e.apply_symm_apply] using (he (e.symm j)).symm
  rw [hj]
  constructor
  · exact sharpQutritCentralOrdered_antitone d (by omega)
  · exact sharpQutritCentralOrdered_antitone d (by omega)

/-- Literal two-coordinate tests show that both central spectral extremes
dominate every external coefficient. For nonnegative diagonal coefficients
these are precisely the external block singular weights. -/
theorem sharpQutritCentralOrdered_dominates_coefficients
    (d : Fin 3 → ℝ) (i : Fin 3) :
    d i ≤ sharpQutritCentralOrdered d 0 ∧ d i ≤ -sharpQutritCentralOrdered d 2 := by
  have hu := hermitian_affine_posSemidef_of_eigenvalues
    (sharpQutritCentralBlock (fun j => (d j : ℂ)))
    (sharpQutritCentralBlock_isHermitian d) (-1) (sharpQutritCentralOrdered d 0)
    (fun j => by
      have h := (sharpQutritCentralEigenvalue_between_extremes d j).2
      change (sharpQutritCentralBlock_isHermitian d).eigenvalues j ≤ _ at h
      linarith)
  have hl := hermitian_affine_posSemidef_of_eigenvalues
    (sharpQutritCentralBlock (fun j => (d j : ℂ)))
    (sharpQutritCentralBlock_isHermitian d) 1 (-sharpQutritCentralOrdered d 2)
    (fun j => by
      have h := (sharpQutritCentralEigenvalue_between_extremes d j).1
      change _ ≤ (sharpQutritCentralBlock_isHermitian d).eigenvalues j at h
      linarith)
  let vp : Fin 3 → Fin 3 → ℂ := ![![0, 1, 1], ![1, 0, 1], ![1, 1, 0]]
  let vm : Fin 3 → Fin 3 → ℂ := ![![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
  have hp := hu.re_dotProduct_nonneg (vp i)
  have hm := hl.re_dotProduct_nonneg (vm i)
  fin_cases i
  all_goals
    norm_num [vp, vm, dotProduct, Matrix.mulVec, Fin.sum_univ_three,
      sharpQutritCentralBlock, Matrix.one_apply, Matrix.smul_apply, Matrix.add_apply,
      Pi.star_apply, Complex.star_def, Complex.mul_re] at hp hm
  · change d 0 ≤ sharpQutritCentralOrdered d 0 ∧
      d 0 ≤ -sharpQutritCentralOrdered d 2
    constructor <;> linarith
  · change d 1 ≤ sharpQutritCentralOrdered d 0 ∧
      d 1 ≤ -sharpQutritCentralOrdered d 2
    constructor <;> linarith
  · change d 2 ≤ sharpQutritCentralOrdered d 0 ∧
      d 2 ≤ -sharpQutritCentralOrdered d 2
    constructor <;> linarith

end ThreeCopyQutritWerner
