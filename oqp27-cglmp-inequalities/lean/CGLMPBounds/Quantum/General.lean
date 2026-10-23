module

public import CGLMPBounds.Defs.QuantumGeneral
public import CGLMPBounds.Statistics.TheoremA4

@[expose] public section


/-!
# Finite-dimensional quantum behaviours with POVMs

* `re_trace_mul_nonneg_of_posSemidef` : `Re Tr(ρ X) ≥ 0` for positive semidefinite `ρ`, `X`
  (diagonalise `ρ`);
* `quantumTable_isNoSignalling` : behaviours of states and POVMs are no-signalling behaviours;
* `quantumTable_phiState` : `⟨Φ_n| Aᵀ ⊗ B |Φ_n⟩ = n⁻¹ Tr(A B)`, so the tracial behaviours of projective
  measurements on `Φ_n` are quantum behaviours (Appendix B's tracial convention);
* `statistical_supremum_povm_spec` : Theorem A.4, "the same supremum holds over arbitrary
  finite-dimensional quantum states and finite-outcome POVMs";
* `isotropic_noise_spec` : Letter, "for these rank-one measurements, probability white noise is
  exactly the behaviour of the maximally mixed bipartite state", and the behaviour of the isotropic
  state `v|Φ_d⟩⟨Φ_d| + (1 - v) I/d²` is the noise mixture `v q + (1 - v) u_d`.
-/

open scoped ComplexOrder Kronecker ENNReal
open Matrix

namespace CGLMPBounds

noncomputable section

/-- `Re Tr(ρ X) ≥ 0` for positive semidefinite `ρ` and `X`. -/
theorem re_trace_mul_nonneg_of_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ρ X : Matrix ι ι ℂ} (hρ : ρ.PosSemidef) (hX : X.PosSemidef) :
    0 ≤ (Matrix.trace (ρ * X)).re := by
  have hspec := hρ.1.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hspec
  obtain ⟨U, hU⟩ : ∃ U : Matrix ι ι ℂ, U = (hρ.1.eigenvectorUnitary : Matrix ι ι ℂ) := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ι → ℂ, D = RCLike.ofReal ∘ hρ.1.eigenvalues := ⟨_, rfl⟩
  rw [← hU, ← hD] at hspec
  have htr : Matrix.trace (ρ * X) = Matrix.trace (Matrix.diagonal D * (star U * X * U)) := by
    rw [hspec, show U * Matrix.diagonal D * star U * X = U * (Matrix.diagonal D * star U * X) by
        simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm U,
      show Matrix.diagonal D * star U * X * U = Matrix.diagonal D * (star U * X * U) by
        simp only [Matrix.mul_assoc]]
  have hM : (star U * X * U).PosSemidef := by
    have h := hX.conjTranspose_mul_mul_same U
    rwa [← Matrix.star_eq_conjTranspose] at h
  rw [htr, Matrix.trace]
  simp only [Matrix.diag, Matrix.diagonal_mul]
  rw [Complex.re_sum]
  refine Finset.sum_nonneg (fun i _ => ?_)
  have hdi : 0 ≤ (star U * X * U) i i := hM.diag_nonneg
  have hev : 0 ≤ hρ.1.eigenvalues i := hρ.eigenvalues_nonneg i
  rw [hD, Function.comp_apply, RCLike.ofReal_eq_complex_ofReal, Complex.re_ofReal_mul]
  exact mul_nonneg hev (Complex.nonneg_iff.mp hdi).1

variable {α β : Type*} [Fintype α] [Fintype β]

theorem sum_kronecker_right {m n : Type*} (E : Matrix m m ℂ) (F : β → Matrix n n ℂ) :
    ∑ b, E ⊗ₖ F b = E ⊗ₖ ∑ b, F b := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp only [Matrix.sum_apply, Matrix.kroneckerMap_apply, Finset.mul_sum]

theorem sum_kronecker_left {m n : Type*} (E : α → Matrix m m ℂ) (F : Matrix n n ℂ) :
    ∑ a, E a ⊗ₖ F = (∑ a, E a) ⊗ₖ F := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp only [Matrix.sum_apply, Matrix.kroneckerMap_apply, Finset.sum_mul]

variable {dA dB : ℕ}

theorem sum_right_quantum {ρ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ}
    {E : Matrix (Fin dA) (Fin dA) ℂ} {F : β → Matrix (Fin dB) (Fin dB) ℂ} (hF : ∑ b, F b = 1) :
    ∑ b, (Matrix.trace (ρ * (E ⊗ₖ F b))).re = (Matrix.trace (ρ * (E ⊗ₖ 1))).re := by
  rw [← Complex.re_sum, ← Matrix.trace_sum, ← Finset.mul_sum, sum_kronecker_right, hF]

theorem sum_left_quantum {ρ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ}
    {E : α → Matrix (Fin dA) (Fin dA) ℂ} {F : Matrix (Fin dB) (Fin dB) ℂ} (hE : ∑ a, E a = 1) :
    ∑ a, (Matrix.trace (ρ * (E a ⊗ₖ F))).re = (Matrix.trace (ρ * (1 ⊗ₖ F))).re := by
  rw [← Complex.re_sum, ← Matrix.trace_sum, ← Finset.mul_sum, sum_kronecker_left, hE]

/-- Behaviours of finite-dimensional states and POVMs are no-signalling behaviours. -/
theorem quantumTable_isNoSignalling {ρ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ}
    {E : Fin 2 → α → Matrix (Fin dA) (Fin dA) ℂ} {F : Fin 2 → β → Matrix (Fin dB) (Fin dB) ℂ}
    (hρ : IsDensityMatrix ρ) (hE : ∀ x, IsPOVM (E x)) (hF : ∀ y, IsPOVM (F y)) :
    IsNoSignalling (quantumTable ρ E F) where
  isBehaviour :=
    { nonneg := fun x y a b => re_trace_mul_nonneg_of_posSemidef hρ.posSemidef
        (((hE x).posSemidef a).kronecker ((hF y).posSemidef b))
      sum_eq_one := fun x y => by
        show ∑ a, ∑ b, (Matrix.trace (ρ * (E x a ⊗ₖ F y b))).re = 1
        simp only [sum_right_quantum (hF y).sum_eq_one]
        rw [sum_left_quantum (hE x).sum_eq_one, Matrix.one_kronecker_one, Matrix.mul_one,
          hρ.trace_eq_one, Complex.one_re] }
  margA_indep := fun x y y' a => by
    show ∑ b, (Matrix.trace (ρ * (E x a ⊗ₖ F y b))).re
      = ∑ b, (Matrix.trace (ρ * (E x a ⊗ₖ F y' b))).re
    rw [sum_right_quantum (hF y).sum_eq_one, sum_right_quantum (hF y').sum_eq_one]
  margB_indep := fun x x' y b => by
    show ∑ a, (Matrix.trace (ρ * (E x a ⊗ₖ F y b))).re
      = ∑ a, (Matrix.trace (ρ * (E x' a ⊗ₖ F y b))).re
    rw [sum_left_quantum (hE x).sum_eq_one, sum_left_quantum (hE x').sum_eq_one]

/-! ### The maximally entangled state -/

theorem star_phiVec (d : ℕ) : star (phiVec d) = phiVec d := by
  funext p
  simp only [Pi.star_apply, phiVec]
  split_ifs
  · exact Complex.conj_ofReal _
  · exact star_zero _

/-- Summing against `|Φ_d⟩` picks the diagonal pairs `(i, i)`. -/
theorem sum_phiVec_mul (d : ℕ) (g : Fin d × Fin d → ℂ) :
    ∑ p, phiVec d p * g p = ∑ i, (((Real.sqrt d)⁻¹ : ℝ) : ℂ) * g (i, i) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
  · simp [phiVec]
  · intro j _ hji
    have hij : i ≠ j := fun h => hji h.symm
    simp [phiVec, hij]

theorem sqrt_inv_mul_self (d : ℕ) [NeZero d] :
    (((Real.sqrt d)⁻¹ : ℝ) : ℂ) * (((Real.sqrt d)⁻¹ : ℝ) : ℂ) = (((d : ℝ)⁻¹ : ℝ) : ℂ) := by
  rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg d)]

/-- `Tr(|Φ_d⟩⟨Φ_d| K) = d⁻¹ Σ_{i,k} K_{(k,k),(i,i)}`. -/
theorem trace_phiState_mul (d : ℕ) [NeZero d] (K : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    Matrix.trace (phiState d * K) = (((d : ℝ)⁻¹ : ℝ) : ℂ) * ∑ i, ∑ k, K (k, k) (i, i) := by
  have e1 : Matrix.trace (phiState d * K) = ∑ p, phiVec d p * ∑ q, phiVec d q * K q p := by
    unfold phiState
    rw [star_phiVec]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.vecMulVec_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
    ring
  rw [e1, sum_phiVec_mul]
  simp only [sum_phiVec_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => ?_))
  rw [← mul_assoc, sqrt_inv_mul_self]

/-- `⟨Φ_d| Aᵀ ⊗ B |Φ_d⟩ = d⁻¹ Tr(A B)`: the tracial behaviours are quantum behaviours on `Φ_d`. -/
theorem quantumTable_phiState {d : ℕ} [NeZero d] (A : Fin 2 → α → Matrix (Fin d) (Fin d) ℂ)
    (B : Fin 2 → β → Matrix (Fin d) (Fin d) ℂ) :
    quantumTable (phiState d) (fun x a => (A x a)ᵀ) B = tracialTable A B := by
  funext x y a b
  show (Matrix.trace (phiState d * ((A x a)ᵀ ⊗ₖ B y b))).re
    = (Matrix.trace (A x a * B y b)).re / d
  rw [trace_phiState_mul, Complex.re_ofReal_mul, div_eq_inv_mul]
  congr 1

theorem phiState_isDensityMatrix (d : ℕ) [NeZero d] : IsDensityMatrix (phiState d) where
  posSemidef := Matrix.posSemidef_vecMulVec_self_star (phiVec d)
  trace_eq_one := by
    have h := trace_phiState_mul d 1
    rw [Matrix.mul_one] at h
    rw [h]
    simp only [Matrix.one_apply, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have hcard : ∑ i : Fin d, ∑ k : Fin d, (if (k, k) = (i, i) then (1 : ℂ) else 0)
        = (d : ℂ) := by
      have hk : ∀ i : Fin d, ∑ k : Fin d, (if (k, k) = (i, i) then (1 : ℂ) else 0) = 1 := by
        intro i
        rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
        · simp
        · intro k _ hki
          simp [hki]
      simp only [hk, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    rw [hcard, Complex.ofReal_inv, Complex.ofReal_natCast,
      inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne d))]

/-- The transposes of the elements of a PVM form a POVM. -/
theorem isPOVM_transpose {n : ℕ} {P : α → Matrix (Fin n) (Fin n) ℂ} (hP : IsPVM P) :
    IsPOVM (fun a => (P a)ᵀ) where
  posSemidef := fun a => by
    have h := Matrix.posSemidef_conjTranspose_mul_self (P a)
    rw [(hP.isHermitian a).eq, hP.mul_self a] at h
    exact h.transpose
  sum_eq_one := by
    rw [← Matrix.transpose_sum, hP.sum_eq_one, Matrix.transpose_one]

/-- A PVM is a POVM. -/
theorem isPOVM_of_isPVM {n : ℕ} {P : α → Matrix (Fin n) (Fin n) ℂ} (hP : IsPVM P) : IsPOVM P where
  posSemidef := fun a => by
    have h := Matrix.posSemidef_conjTranspose_mul_self (P a)
    rwa [(hP.isHermitian a).eq, hP.mul_self a] at h
  sum_eq_one := hP.sum_eq_one

theorem tracialTable_mem_quantumBehaviours {d : ℕ} [NeZero d]
    {A : Fin 2 → α → Matrix (Fin d) (Fin d) ℂ} {B : Fin 2 → β → Matrix (Fin d) (Fin d) ℂ}
    (hA : ∀ x, IsPVM (A x)) (hB : ∀ y, IsPVM (B y)) :
    tracialTable A B ∈ quantumBehaviours α β :=
  ⟨d, d, phiState d, fun x a => (A x a)ᵀ, B, phiState_isDensityMatrix d,
    fun x => isPOVM_transpose (hA x), fun y => isPOVM_of_isPVM (hB y),
    (quantumTable_phiState A B).symm⟩

theorem rankOnePVMBehaviours_subset {d : ℕ} (hd : 2 ≤ d) :
    rankOnePVMBehaviours d ⊆ quantumBehaviours (Fin d) (Fin d) := by
  rintro q ⟨A, B, hA, hB, rfl⟩
  haveI : NeZero d := ⟨by omega⟩
  exact tracialTable_mem_quantumBehaviours (fun x => (hA x).1) (fun y => (hB y).1)

/-- **Theorem A.4, POVM part.** For every input law, the supremum of the statistical strength over
`d ≥ 2` and all behaviours of finite-dimensional states and `d`-outcome POVMs equals `Ξ(μ)`. -/
theorem statistical_supremum_povm_spec {μ : Fin 2 → Fin 2 → ℝ} (hμ : ∀ x y, 0 ≤ μ x y)
    (hμ1 : ∑ x, ∑ y, μ x y = 1) :
    ⨆ (d : ℕ) (_ : 2 ≤ d) (q ∈ quantumBehaviours (Fin d) (Fin d)),
      statStrength μ q = xiMin μ := by
  apply le_antisymm
  · refine iSup_le (fun d => iSup_le (fun _ => iSup₂_le (fun q hq => ?_)))
    obtain ⟨dA, dB, ρ, E, F, hρ, hE, hF, rfl⟩ := hq
    have hns := quantumTable_isNoSignalling hρ hE hF
    exact (statistical_ceiling_spec hns hμ hμ1).1.trans (statistical_ceiling_spec hns hμ hμ1).2
  · rw [← statistical_supremum_spec hμ hμ1]
    exact iSup_mono (fun d => iSup_mono (fun hd =>
      biSup_mono (fun q hq => rankOnePVMBehaviours_subset hd hq)))

/-! ### White noise and the isotropic state -/

/-- `quantumTable` is real-linear in the state. -/
theorem quantumTable_add_smul {ρ₁ ρ₂ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ} (s t : ℝ)
    (E : Fin 2 → α → Matrix (Fin dA) (Fin dA) ℂ) (F : Fin 2 → β → Matrix (Fin dB) (Fin dB) ℂ) :
    quantumTable (((s : ℝ) : ℂ) • ρ₁ + ((t : ℝ) : ℂ) • ρ₂) E F
      = s • quantumTable ρ₁ E F + t • quantumTable ρ₂ E F := by
  funext x y a b
  simp only [quantumTable, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.add_mul,
    Matrix.smul_mul, Matrix.trace_add, Matrix.trace_smul, Complex.add_re]
  rw [Complex.re_ofReal_mul, Complex.re_ofReal_mul]

/-- **Letter, white noise.** For rank-one projective measurements on `ℂ^d` (Alice's in the tracial,
transposed form), the maximally mixed state `I/d²` produces the uniform table `u_d`, and the
isotropic state `v|Φ_d⟩⟨Φ_d| + (1 - v) I/d²` produces the noise mixture `v q + (1 - v) u_d` of the
behaviour `q` on `Φ_d`. -/
theorem isotropic_noise_spec {d : ℕ} [NeZero d] {A B : Fin 2 → Fin d → Matrix (Fin d) (Fin d) ℂ}
    (hA : ∀ x, IsRankOnePVM (A x)) (hB : ∀ y, IsRankOnePVM (B y)) (v : ℝ) :
    quantumTable (((1 / (d : ℝ) ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ))
        (fun x a => (A x a)ᵀ) B = uniformTable (Fin d) (Fin d) ∧
      quantumTable (((v : ℝ) : ℂ) • phiState d
          + (((1 - v) / (d : ℝ) ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ))
        (fun x a => (A x a)ᵀ) B = noisy v (tracialTable A B) := by
  have hmixed : quantumTable (((1 / (d : ℝ) ^ 2 : ℝ) : ℂ)
      • (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)) (fun x a => (A x a)ᵀ) B
      = uniformTable (Fin d) (Fin d) := by
    funext x y a b
    show (Matrix.trace ((((1 / (d : ℝ) ^ 2 : ℝ) : ℂ)
        • (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)) * ((A x a)ᵀ ⊗ₖ B y b))).re
      = 1 / ((Fintype.card (Fin d) : ℝ) * (Fintype.card (Fin d) : ℝ))
    rw [Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul, Matrix.trace_kronecker,
      Matrix.trace_transpose, (hA x).2 a, (hB y).2 b, mul_one, smul_eq_mul, mul_one,
      Complex.ofReal_re, Fintype.card_fin]
    ring
  refine ⟨hmixed, ?_⟩
  have hsplit : (((1 - v) / (d : ℝ) ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
      = (((1 - v : ℝ)) : ℂ) • ((((1 / (d : ℝ) ^ 2 : ℝ) : ℂ))
        • (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)) := by
    rw [smul_smul, ← Complex.ofReal_mul]
    congr 2
    ring
  rw [hsplit, quantumTable_add_smul, hmixed, quantumTable_phiState]
  rfl

end

end CGLMPBounds
