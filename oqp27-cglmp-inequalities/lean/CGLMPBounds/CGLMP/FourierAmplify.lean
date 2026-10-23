module

public import CGLMPBounds.CGLMP.FourierAttain
public import CGLMPBounds.Fourier.Basis

@[expose] public section


/-!
# The standard amplifications attain `I_d^F`

Theorem A.1: "Equality holds if … `n = dk` and, after a common unitary conjugation in the tracial
representation, the four PVMs are `Π^t_a ⊗ I_k`"; Theorem A.3: "the minimum is attained whenever
`d | n`". For `n = dk` and a unitary `U` on `ℂ^{dk}`, the tracial PVMs `U (Π^t_a ⊗ I_k) U*`
(`ℂ^d ⊗ ℂ^k ≅ ℂ^{dk}` by `finProdFinEquiv`) have the tracial behaviour `Q_d` on `Φ_{dk}`; hence
`I_d = I_d^F`, and the noisy mixture violates the CGLMP inequality exactly above `2/I_d^F`.

* `amplify U P = U (P ⊗ I_k) U*`;
* `amplify_mul`, `trace_amplify` : `amplify U P * amplify U Q = amplify U (P Q)`,
  `Tr(amplify U P) = k Tr P`;
* `isPVM_amplify` : amplified PVMs are PVMs;
* `tracialTable_amplify_fourier` : the amplified Fourier measurements have the tracial table `Q_d`;
* `fourier_amplification_attains_spec` : the form of the Challenge endpoint (`Matrix.kronecker`
  there, the notation `⊗ₖ`, i.e. `kroneckerMap (· * ·)`, here; the two are definitionally equal).
-/

open Matrix
open scoped Kronecker

namespace CGLMPBounds

noncomputable section

variable {d k : ℕ}

/-- `U (P ⊗ I_k) U*` on `ℂ^{dk}`. -/
def amplify (U : Matrix (Fin (d * k)) (Fin (d * k)) ℂ) (P : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin (d * k)) (Fin (d * k)) ℂ :=
  U * Matrix.reindex finProdFinEquiv finProdFinEquiv (P ⊗ₖ (1 : Matrix (Fin k) (Fin k) ℂ)) * star U

theorem trace_submatrix_equiv {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m m ℂ)
    (e : n ≃ m) : Matrix.trace (A.submatrix e e) = Matrix.trace A := by
  simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
  exact Equiv.sum_comp e (fun i => A i i)

theorem reindex_kron_mul (P Q : Matrix (Fin d) (Fin d) ℂ) :
    Matrix.reindex finProdFinEquiv finProdFinEquiv (P ⊗ₖ (1 : Matrix (Fin k) (Fin k) ℂ))
      * Matrix.reindex finProdFinEquiv finProdFinEquiv (Q ⊗ₖ (1 : Matrix (Fin k) (Fin k) ℂ))
      = Matrix.reindex finProdFinEquiv finProdFinEquiv
          ((P * Q) ⊗ₖ (1 : Matrix (Fin k) (Fin k) ℂ)) := by
  rw [Matrix.reindex_apply, Matrix.reindex_apply, Matrix.reindex_apply,
    Matrix.submatrix_mul_equiv, ← Matrix.mul_kronecker_mul, Matrix.mul_one]

theorem amplify_mul {U : Matrix (Fin (d * k)) (Fin (d * k)) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin (d * k)) ℂ) (P Q : Matrix (Fin d) (Fin d) ℂ) :
    amplify U P * amplify U Q = amplify U (P * Q) := by
  have hUU : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  unfold amplify
  rw [← reindex_kron_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (star U) U, hUU, Matrix.one_mul]

theorem trace_amplify {U : Matrix (Fin (d * k)) (Fin (d * k)) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin (d * k)) ℂ) (P : Matrix (Fin d) (Fin d) ℂ) :
    Matrix.trace (amplify U P) = (k : ℂ) * Matrix.trace P := by
  have hUU : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  unfold amplify
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hUU, Matrix.one_mul, Matrix.reindex_apply,
    trace_submatrix_equiv, Matrix.trace_kronecker, Matrix.trace_one, Fintype.card_fin, mul_comm]

theorem isPVM_amplify {α : Type*} [Fintype α] {U : Matrix (Fin (d * k)) (Fin (d * k)) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin (d * k)) ℂ) {P : α → Matrix (Fin d) (Fin d) ℂ}
    (hP : IsPVM P) : IsPVM (fun a => amplify U (P a)) where
  isHermitian a := by
    unfold amplify Matrix.IsHermitian
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_reindex,
      Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, (hP.isHermitian a).eq,
      Matrix.mul_assoc]
  mul_self a := by rw [amplify_mul hU, hP.mul_self a]
  sum_eq_one := by
    have hUU' : U * star U = 1 := Matrix.mem_unitaryGroup_iff.mp hU
    unfold amplify
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    have hkron : ∑ a, P a ⊗ₖ (1 : Matrix (Fin k) (Fin k) ℂ)
        = (∑ a, P a) ⊗ₖ (1 : Matrix (Fin k) (Fin k) ℂ) := by
      ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
      simp only [Matrix.sum_apply, Matrix.kroneckerMap_apply, Finset.sum_mul]
    have hre : ∑ a, Matrix.reindex finProdFinEquiv finProdFinEquiv
        (P a ⊗ₖ (1 : Matrix (Fin k) (Fin k) ℂ))
        = Matrix.reindex finProdFinEquiv finProdFinEquiv
            (∑ a, P a ⊗ₖ (1 : Matrix (Fin k) (Fin k) ℂ)) := by
      ext i j
      simp only [Matrix.sum_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
    have hsum : ∑ a, Matrix.reindex finProdFinEquiv finProdFinEquiv
        (P a ⊗ₖ (1 : Matrix (Fin k) (Fin k) ℂ)) = 1 := by
      rw [hre, hkron, hP.sum_eq_one, Matrix.one_kronecker_one, Matrix.reindex_apply,
        Matrix.submatrix_one_equiv]
    rw [hsum, Matrix.mul_one, hUU']

/-- The amplified Fourier measurements on `Φ_{dk}` have the tracial table `Q_d`. -/
theorem tracialTable_amplify_fourier [NeZero d] [NeZero k]
    {U : Matrix (Fin (d * k)) (Fin (d * k)) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin (d * k)) ℂ) :
    tracialTable (fun x a => amplify U (fourierProjector d (2 * x.val) a))
        (fun y b => amplify U (fourierProjector d (1 + 2 * y.val) b))
      = fourierTable d := by
  have hk : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne k)
  funext x y a b
  unfold fourierTable tracialTable
  rw [amplify_mul hU, trace_amplify hU, Nat.cast_mul]
  have e : ((k : ℂ) * Matrix.trace (fourierProjector d (2 * x.val) a
      * fourierProjector d (1 + 2 * y.val) b)).re
      = (k : ℝ) * (Matrix.trace (fourierProjector d (2 * x.val) a
        * fourierProjector d (1 + 2 * y.val) b)).re := by
    rw [← Complex.ofReal_natCast, Complex.re_ofReal_mul]
  rw [e, mul_comm (d : ℝ) (k : ℝ), mul_div_mul_left _ _ hk]

/-- The form of the Challenge endpoint, with the amplified measurements given by a defining
equation `P t a = U (Π^t_a ⊗ I_k) U*`. -/
theorem fourier_amplification_attains_spec [NeZero d] [NeZero k] (hd : 2 ≤ d)
    {U : Matrix (Fin (d * k)) (Fin (d * k)) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin (d * k)) ℂ)
    {P : ℕ → ZMod d → Matrix (Fin (d * k)) (Fin (d * k)) ℂ}
    (hP : ∀ t a, P t a = U * Matrix.reindex finProdFinEquiv finProdFinEquiv
      (Matrix.kronecker (fourierProjector d t a) (1 : Matrix (Fin k) (Fin k) ℂ)) * star U) :
    (∀ t, IsPVM (P t)) ∧
      cglmp d (tracialTable (fun x a => P (2 * x.val) a) (fun y b => P (1 + 2 * y.val) b))
        = cglmpFourierValue d ∧
      ∀ v : ℝ, 2 < cglmp d (noisy v (tracialTable (fun x a => P (2 * x.val) a)
          (fun y b => P (1 + 2 * y.val) b))) ↔ 2 / cglmpFourierValue d < v := by
  have hA : (fun (x : Fin 2) (a : ZMod d) => P (2 * x.val) a)
      = fun x a => amplify U (fourierProjector d (2 * x.val) a) := by
    funext x a
    exact hP _ _
  have hB : (fun (y : Fin 2) (b : ZMod d) => P (1 + 2 * y.val) b)
      = fun y b => amplify U (fourierProjector d (1 + 2 * y.val) b) := by
    funext y b
    exact hP _ _
  have hT := tracialTable_amplify_fourier (d := d) (k := k) hU
  refine ⟨fun t => ?_, ?_, fun v => ?_⟩
  · have hPt : P t = fun a => amplify U (fourierProjector d t a) := funext (hP t)
    rw [hPt]
    exact isPVM_amplify hU (fourierProjector_isPVM d t)
  · rw [hA, hB, hT]
    exact cglmp_fourierTable d hd
  · rw [hA, hB, hT]
    exact (fourier_attains_cglmp_value_spec d hd).2.2 v

end

end CGLMPBounds
