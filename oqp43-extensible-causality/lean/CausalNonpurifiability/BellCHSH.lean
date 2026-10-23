module

public import CausalNonpurifiability.Certificates.Qubit
public import CausalNonpurifiability.Linear.Positive

@[expose] public section


/-!
# `CausalNonpurifiability.BellCHSH`

`rem:Bell` (b): for the weights `(1, 1, 1, -1)` of CHSH the operator
inequality corresponding to Lemma 5.2 is false. On `ℂ² ⊗ ℂ²` take `𝖠_0 = Z ⊗ I`, `𝖠_1 = X ⊗ I`,
`𝖡_0 = I ⊗ (3Z + 4X)/5`, `𝖡_1 = I ⊗ (3Z - 4X)/5` and the effects `E_i = (I - 𝖠_i)/2`,
`H_j = (I - 𝖡_j)/2` (rational projections; `E_i H_j = H_j E_i`). Then
`D_00 + D_01 + D_10 - D_11` has the principal minor `[[2/5, -4/5], [-4/5, 2/5]]` on
`|00⟩, |11⟩`, of determinant `-12/25 < 0`.
-/

set_option autoImplicit false

open Matrix
open scoped Kronecker ComplexOrder

namespace CausalNonpurifiability

/-- `E_0 = (I - Z)/2 ⊗ I`. -/
def chshE0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℚ :=
  !![0, 0; 0, 1] ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℚ)
/-- `E_1 = (I - X)/2 ⊗ I`. -/
def chshE1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℚ :=
  !![1 / 2, -1 / 2; -1 / 2, 1 / 2] ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℚ)
/-- `H_0 = I ⊗ (I - (3Z + 4X)/5)/2`. -/
def chshH0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℚ :=
  (1 : Matrix (Fin 2) (Fin 2) ℚ) ⊗ₖ !![1 / 5, -2 / 5; -2 / 5, 4 / 5]
/-- `H_1 = I ⊗ (I - (3Z - 4X)/5)/2`. -/
def chshH1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℚ :=
  (1 : Matrix (Fin 2) (Fin 2) ℚ) ⊗ₖ !![1 / 5, 2 / 5; 2 / 5, 4 / 5]

/-- The CHSH combination `D_00 + D_01 + D_10 - D_11` with `D_ij = E_i + H_j - 2 E_i H_j`. -/
def chshS : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℚ :=
  (chshE0 + chshH0 - (2 : ℚ) • (chshE0 * chshH0)) + (chshE0 + chshH1 - (2 : ℚ) • (chshE0 * chshH1)) +
    (chshE1 + chshH0 - (2 : ℚ) • (chshE1 * chshH0)) - (chshE1 + chshH1 - (2 : ℚ) • (chshE1 * chshH1))

theorem chsh_projections :
    chshE0ᵀ = chshE0 ∧ chshE0 * chshE0 = chshE0 ∧ chshE1ᵀ = chshE1 ∧ chshE1 * chshE1 = chshE1 ∧
    chshH0ᵀ = chshH0 ∧ chshH0 * chshH0 = chshH0 ∧ chshH1ᵀ = chshH1 ∧ chshH1 * chshH1 = chshH1 := by
  decide +kernel

theorem chsh_commute :
    chshE0 * chshH0 = chshH0 * chshE0 ∧ chshE0 * chshH1 = chshH1 * chshE0 ∧
    chshE1 * chshH0 = chshH0 * chshE1 ∧ chshE1 * chshH1 = chshH1 * chshE1 := by
  decide +kernel

theorem chshS_entries :
    chshS (0, 0) (0, 0) = 2 / 5 ∧ chshS (0, 0) (1, 1) = -4 / 5 ∧ chshS (1, 1) (0, 0) = -4 / 5 ∧
    chshS (1, 1) (1, 1) = 2 / 5 := by
  decide +kernel

theorem effect_toC_of_proj {ι : Type} [Fintype ι] [DecidableEq ι] {P : Matrix ι ι ℚ}
    (hT : Pᵀ = P) (hP : P * P = P) : Effect (toC P) := by
  refine ⟨transpose_mul_self_sound P P 1 (by rw [hT, hP, one_smul]) (by norm_num), ?_⟩
  have h1 : (1 : Matrix ι ι ℂ) - toC P = toC (1 - P) := by rw [toC_sub, toC_one]
  rw [h1]
  refine transpose_mul_self_sound (1 - P) (1 - P) 1 ?_ (by norm_num)
  rw [Matrix.transpose_sub, Matrix.transpose_one, hT, one_smul]
  simp only [sub_mul, mul_sub, one_mul, mul_one, hP, sub_self, sub_zero]

theorem toC_mul_rat {ι : Type} [Fintype ι] (A B : Matrix ι ι ℚ) : toC A * toC B = toC (A * B) :=
  (Matrix.map_mul).symm

/-- **`rem:Bell`** (b): for the CHSH weights `(1, 1, 1, -1)` the operator
inequality of Lemma 5.2 fails: there are effects `E_0, E_1, H_0, H_1` with `E_i H_j = H_j E_i`
such that `D_00 + D_01 + D_10 - D_11` is not positive. -/
theorem rem_bell_b :
    ∃ E0 E1 H0 H1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ,
      Effect E0 ∧ Effect E1 ∧ Effect H0 ∧ Effect H1 ∧
      E0 * H0 = H0 * E0 ∧ E0 * H1 = H1 * E0 ∧ E1 * H0 = H0 * E1 ∧ E1 * H1 = H1 * E1 ∧
      ¬ ((E0 + H0 - (2 : ℂ) • (E0 * H0)) + (E0 + H1 - (2 : ℂ) • (E0 * H1)) +
          (E1 + H0 - (2 : ℂ) • (E1 * H0)) - (E1 + H1 - (2 : ℂ) • (E1 * H1))).PosSemidef := by
  obtain ⟨t0, p0, t1, p1, s0, q0, s1, q1⟩ := chsh_projections
  obtain ⟨c00, c01, c10, c11⟩ := chsh_commute
  obtain ⟨e00, e01, e10, e11⟩ := chshS_entries
  refine ⟨toC chshE0, toC chshE1, toC chshH0, toC chshH1, effect_toC_of_proj t0 p0,
    effect_toC_of_proj t1 p1, effect_toC_of_proj s0 q0, effect_toC_of_proj s1 q1, ?_, ?_, ?_, ?_, ?_⟩
  · rw [toC_mul_rat, toC_mul_rat, c00]
  · rw [toC_mul_rat, toC_mul_rat, c01]
  · rw [toC_mul_rat, toC_mul_rat, c10]
  · rw [toC_mul_rat, toC_mul_rat, c11]
  · intro hpsd
    have hS : (toC chshE0 + toC chshH0 - (2 : ℂ) • (toC chshE0 * toC chshH0)) +
        (toC chshE0 + toC chshH1 - (2 : ℂ) • (toC chshE0 * toC chshH1)) +
        (toC chshE1 + toC chshH0 - (2 : ℂ) • (toC chshE1 * toC chshH0)) -
        (toC chshE1 + toC chshH1 - (2 : ℂ) • (toC chshE1 * toC chshH1)) = toC chshS := by
      simp only [chshS, toC_add, toC_sub, toC_smul, toC_mul_rat]
      norm_num
    rw [hS] at hpsd
    have hdet := (hpsd.submatrix (![(0, 0), (1, 1)] : Fin 2 → Fin 2 × Fin 2)).det_nonneg
    rw [Matrix.det_fin_two] at hdet
    simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      toC_apply, e00, e01, e10, e11] at hdet
    have hv : ((2 / 5 : ℚ) : ℂ) * ((2 / 5 : ℚ) : ℂ) - ((-4 / 5 : ℚ) : ℂ) * ((-4 / 5 : ℚ) : ℂ) =
        ((-12 / 25 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hv, Complex.zero_le_real] at hdet
    norm_num at hdet

end CausalNonpurifiability
