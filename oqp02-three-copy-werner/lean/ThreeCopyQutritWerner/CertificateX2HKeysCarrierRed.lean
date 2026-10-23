module

public import ThreeCopyQutritWerner.CertificateX2HKeysTrace
public import ThreeCopyQutritWerner.CertificateX2HKeysRedCheck
public import ThreeCopyQutritWerner.CertificateX2HKeysMulCheck

@[expose] public section


/-!
# `carrier_fix` from three transposition identities per key

The sector-0 carrier element is `E = ∑_p (num_p / 96) g_p = e_A e_χ` in the group algebra of the
carrier permutations, with `e_A = (1 - (1 2))(1 - (3 4)) / 4` and `e_χ = χ_[3,2] / 24 =
∏_{c ∈ {10, 5, 0, -2, -5, -10}} (T - c) / (2 - c)`, `T` the sum of the ten transpositions
(kernel checks: CertificateX2HKeysRedCheck). With the multiplicativity of the per-site actions on
the special left factors (CertificateX2HKeysMulCheck), the triple action `x2hRho` turns these
identities into operator identities, so for any matrix `J` of frame vectors:

`ρ((1 2)) J = -J`, `ρ((3 4)) J = -J`, `ρ(T) J = 2 J`  ⟹  `x2hCarrier τ * J = J` (`x2hCarrierFix_of_transp`).
-/

set_option maxRecDepth 100000

noncomputable section

open scoped BigOperators Matrix Kronecker

namespace ThreeCopyQutritWerner.X2Sites

open X2

/-- The diagonal triple action of one carrier permutation (one term of `x2hCarrier`). -/
def rhoG (τ : Fin 7 × Fin 7 × Fin 7) (p : Fin 120) : Matrix (HIdx τ) (HIdx τ) ℂ :=
  x2hTriple (x2hAct p) (x2hAct p) (x2hAct p) τ

/-- The triple action of a coefficient vector on the carrier permutations. -/
def x2hRho (τ : Fin 7 × Fin 7 × Fin 7) (X : Fin 120 → ℂ) : Matrix (HIdx τ) (HIdx τ) ℂ :=
  ∑ p, X p • rhoG τ p

theorem x2hCarrier_rho (τ : Fin 7 × Fin 7 × Fin 7) :
    x2hCarrier τ = x2hRho τ (fun p => (x2hWeight p : ℂ)) := rfl

/-! ## Multiplicativity -/

theorem triple_mul (A B C A' B' C' : HFam) (τ : Fin 7 × Fin 7 × Fin 7) :
    x2hTriple A B C τ * x2hTriple A' B' C' τ =
      x2hTriple (fun t => A t * A' t) (fun t => B t * B' t) (fun t => C t * C' t) τ := by
  unfold x2hTriple
  rw [Matrix.submatrix_mul_equiv, ← Matrix.mul_kronecker_mul, Matrix.submatrix_mul_equiv,
    ← Matrix.mul_kronecker_mul]

theorem x2hAct_mul (s : Fin 12) (q : Fin 120) (t : Fin 7) :
    x2hAct (x2hSpecial s) t * x2hAct q t = x2hAct (x2hLMul s q) t := by
  fin_cases t
  · show (x2hA0 (x2hSpecial s)).map (Int.cast : ℤ → ℂ) * (x2hA0 q).map (Int.cast : ℤ → ℂ) =
      (x2hA0 (x2hLMul s q)).map (Int.cast : ℤ → ℂ)
    rw [map_int_mul, x2hMulCheck0 s q]
  · show (x2hA1 (x2hSpecial s)).map (Int.cast : ℤ → ℂ) * (x2hA1 q).map (Int.cast : ℤ → ℂ) =
      (x2hA1 (x2hLMul s q)).map (Int.cast : ℤ → ℂ)
    rw [map_int_mul, x2hMulCheck1 s q]
  · show (x2hA2 (x2hSpecial s)).map (Int.cast : ℤ → ℂ) * (x2hA2 q).map (Int.cast : ℤ → ℂ) =
      (x2hA2 (x2hLMul s q)).map (Int.cast : ℤ → ℂ)
    rw [map_int_mul, x2hMulCheck2 s q]
  · show (x2hA3 (x2hSpecial s)).map (Int.cast : ℤ → ℂ) * (x2hA3 q).map (Int.cast : ℤ → ℂ) =
      (x2hA3 (x2hLMul s q)).map (Int.cast : ℤ → ℂ)
    rw [map_int_mul, x2hMulCheck3 s q]
  · show (x2hA4 (x2hSpecial s)).map (Int.cast : ℤ → ℂ) * (x2hA4 q).map (Int.cast : ℤ → ℂ) =
      (x2hA4 (x2hLMul s q)).map (Int.cast : ℤ → ℂ)
    rw [map_int_mul, x2hMulCheck4 s q]
  · show (x2hA5 (x2hSpecial s)).map (Int.cast : ℤ → ℂ) * (x2hA5 q).map (Int.cast : ℤ → ℂ) =
      (x2hA5 (x2hLMul s q)).map (Int.cast : ℤ → ℂ)
    rw [map_int_mul, x2hMulCheck5 s q]
  · show (x2hA6 (x2hSpecial s)).map (Int.cast : ℤ → ℂ) * (x2hA6 q).map (Int.cast : ℤ → ℂ) =
      (x2hA6 (x2hLMul s q)).map (Int.cast : ℤ → ℂ)
    rw [map_int_mul, x2hMulCheck6 s q]

theorem x2hAct_one (t : Fin 7) : x2hAct (x2hSpecial 0) t = 1 := by
  fin_cases t
  · show (x2hA0 (x2hSpecial 0)).map (Int.cast : ℤ → ℂ) = 1
    rw [x2hIdCheck0, Matrix.map_one _ Int.cast_zero Int.cast_one]
  · show (x2hA1 (x2hSpecial 0)).map (Int.cast : ℤ → ℂ) = 1
    rw [x2hIdCheck1, Matrix.map_one _ Int.cast_zero Int.cast_one]
  · show (x2hA2 (x2hSpecial 0)).map (Int.cast : ℤ → ℂ) = 1
    rw [x2hIdCheck2, Matrix.map_one _ Int.cast_zero Int.cast_one]
  · show (x2hA3 (x2hSpecial 0)).map (Int.cast : ℤ → ℂ) = 1
    rw [x2hIdCheck3, Matrix.map_one _ Int.cast_zero Int.cast_one]
  · show (x2hA4 (x2hSpecial 0)).map (Int.cast : ℤ → ℂ) = 1
    rw [x2hIdCheck4, Matrix.map_one _ Int.cast_zero Int.cast_one]
  · show (x2hA5 (x2hSpecial 0)).map (Int.cast : ℤ → ℂ) = 1
    rw [x2hIdCheck5, Matrix.map_one _ Int.cast_zero Int.cast_one]
  · show (x2hA6 (x2hSpecial 0)).map (Int.cast : ℤ → ℂ) = 1
    rw [x2hIdCheck6, Matrix.map_one _ Int.cast_zero Int.cast_one]

theorem rhoG_mul (τ : Fin 7 × Fin 7 × Fin 7) (s : Fin 12) (q : Fin 120) :
    rhoG τ (x2hSpecial s) * rhoG τ q = rhoG τ (x2hLMul s q) := by
  unfold rhoG
  rw [triple_mul]
  first
    | (simp only [x2hAct_mul]; done)
    | (congr 1 <;> funext t <;> exact x2hAct_mul s q t)

theorem rhoG_one (τ : Fin 7 × Fin 7 × Fin 7) : rhoG τ (x2hSpecial 0) = 1 := by
  unfold rhoG x2hTriple
  simp only [x2hAct_one, Matrix.one_kronecker_one, Matrix.submatrix_one_equiv]

theorem x2hLMul_bij (s : Fin 12) : Function.Bijective (x2hLMul s) :=
  Function.bijective_iff_has_inverse.mpr ⟨x2hLDiv s, x2hDivMul s, x2hMulDiv s⟩

/-- Left multiplication by a special element shifts the coefficient vector. -/
theorem rho_left (τ : Fin 7 × Fin 7 × Fin 7) (s : Fin 12) (Y : Fin 120 → ℂ) :
    rhoG τ (x2hSpecial s) * x2hRho τ Y = x2hRho τ (fun r => Y (x2hLDiv s r)) := by
  unfold x2hRho
  rw [Matrix.mul_sum]
  simp only [Matrix.mul_smul, rhoG_mul]
  rw [← (x2hLMul_bij s).sum_comp (fun r => Y (x2hLDiv s r) • rhoG τ r)]
  simp only [x2hDivMul]

/-! ## Linearity -/

theorem x2hRho_add (τ : Fin 7 × Fin 7 × Fin 7) (X Y : Fin 120 → ℂ) :
    x2hRho τ (fun p => X p + Y p) = x2hRho τ X + x2hRho τ Y := by
  unfold x2hRho
  simp only [add_smul, Finset.sum_add_distrib]

theorem x2hRho_sub (τ : Fin 7 × Fin 7 × Fin 7) (X Y : Fin 120 → ℂ) :
    x2hRho τ (fun p => X p - Y p) = x2hRho τ X - x2hRho τ Y := by
  unfold x2hRho
  simp only [sub_smul, Finset.sum_sub_distrib]

theorem x2hRho_cmul (τ : Fin 7 × Fin 7 × Fin 7) (c : ℂ) (X : Fin 120 → ℂ) :
    x2hRho τ (fun p => c * X p) = c • x2hRho τ X := by
  unfold x2hRho
  simp only [mul_smul, Finset.smul_sum]

theorem x2hRho_sum (τ : Fin 7 × Fin 7 × Fin 7) {ι : Type*} (s : Finset ι) (X : ι → Fin 120 → ℂ) :
    x2hRho τ (fun p => ∑ i ∈ s, X i p) = ∑ i ∈ s, x2hRho τ (X i) := by
  unfold x2hRho
  simp only [Finset.sum_smul]
  exact Finset.sum_comm

/-! ## The `[3,2]` idempotent -/

theorem x2hRho_Q0 (τ : Fin 7 × Fin 7 × Fin 7) : x2hRho τ (fun r => (x2hQ 0 r : ℂ)) = 1 := by
  unfold x2hRho
  simp only [x2hQ0]
  push_cast
  simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact rhoG_one τ

theorem rhoQ_succ (τ : Fin 7 × Fin 7 × Fin 7) (i : Fin 6) :
    x2hRho τ (fun r => (x2hQ i.succ r : ℂ)) =
      (∑ u : Fin 10, rhoG τ (x2hSpecial u.succ.castSucc)) * x2hRho τ (fun r => (x2hQ i.castSucc r : ℂ)) -
        (x2hCt i : ℂ) • x2hRho τ (fun r => (x2hQ i.castSucc r : ℂ)) := by
  have h : (fun r => (x2hQ i.succ r : ℂ)) = fun r =>
      (∑ u : Fin 10, (x2hQ i.castSucc (x2hLDiv u.succ.castSucc r) : ℂ)) - (x2hCt i : ℂ) * (x2hQ i.castSucc r : ℂ) := by
    funext r
    simp only [x2hQstep i r, Int.cast_sub, Int.cast_sum, Int.cast_mul]
  rw [h, x2hRho_sub, x2hRho_sum, x2hRho_cmul, Matrix.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro u _
  rw [rho_left]

theorem rhoQ_fix (τ : Fin 7 × Fin 7 × Fin 7) {κ : Type*} (J : Matrix (HIdx τ) κ ℂ)
    (hT : (∑ u : Fin 10, rhoG τ (x2hSpecial u.succ.castSucc)) * J = (2 : ℂ) • J) (i : Fin 7) :
    x2hRho τ (fun r => (x2hQ i r : ℂ)) * J = (x2hD i : ℂ) • J := by
  induction i using Fin.induction with
  | zero =>
    rw [x2hRho_Q0, Matrix.one_mul, x2hD0]
    simp
  | succ i ih =>
    rw [rhoQ_succ, Matrix.sub_mul, Matrix.mul_assoc, ih, Matrix.mul_smul, hT, Matrix.smul_mul, ih,
      x2hDstep, smul_smul, smul_smul, ← sub_smul]
    congr 1
    push_cast
    ring

/-! ## The carrier -/

theorem x2hCarrierFix_of_transp (τ : Fin 7 × Fin 7 × Fin 7) {κ : Type*} (J : Matrix (HIdx τ) κ ℂ)
    (h12 : rhoG τ (x2hSpecial 5) * J = -J) (h34 : rhoG τ (x2hSpecial 10) * J = -J)
    (hT : (∑ u : Fin 10, rhoG τ (x2hSpecial u.succ.castSucc)) * J = (2 : ℂ) • J) :
    x2hCarrier τ * J = J := by
  have h6 := rhoQ_fix τ J hT 6
  have e6 : (fun r => (x2hQ 6 r : ℂ)) = fun r => (672 : ℂ) * (x2hChi r : ℂ) := by
    funext r
    simp only [x2hQ6 r, Int.cast_mul, Int.cast_ofNat]
  rw [e6, x2hRho_cmul, x2hD6, Matrix.smul_mul] at h6
  have h672 : (672 : ℂ) ≠ 0 := by norm_num
  have hchi : x2hRho τ (fun r => (x2hChi r : ℂ)) * J = (24 : ℂ) • J := by
    calc x2hRho τ (fun r => (x2hChi r : ℂ)) * J
        = (672 : ℂ)⁻¹ • ((672 : ℂ) • (x2hRho τ (fun r => (x2hChi r : ℂ)) * J)) := by
          rw [smul_smul, inv_mul_cancel₀ h672, one_smul]
      _ = (672 : ℂ)⁻¹ • (((16128 : ℤ) : ℂ) • J) := by rw [h6]
      _ = (24 : ℂ) • J := by
          rw [smul_smul]
          norm_num
  have h11 : rhoG τ (x2hSpecial 11) * J = J := by
    rw [← x2hSpecial11, ← rhoG_mul, Matrix.mul_assoc, h34, Matrix.mul_neg, h12, neg_neg]
  have hnum : (fun r => (x2hNum r : ℂ)) = fun r => (x2hChi r : ℂ) - (x2hChi (x2hLDiv 5 r) : ℂ) -
      (x2hChi (x2hLDiv 10 r) : ℂ) + (x2hChi (x2hLDiv 11 r) : ℂ) := by
    funext r
    simp only [x2hNumChi r, Int.cast_add, Int.cast_sub]
  have hE : x2hRho τ (fun r => (x2hNum r : ℂ)) * J = (96 : ℂ) • J := by
    rw [hnum, x2hRho_add, x2hRho_sub, x2hRho_sub, ← rho_left τ 5 (fun r => (x2hChi r : ℂ)),
      ← rho_left τ 10 (fun r => (x2hChi r : ℂ)), ← rho_left τ 11 (fun r => (x2hChi r : ℂ))]
    rw [Matrix.add_mul, Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc,
      hchi, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_smul, h12, h34, h11]
    simp only [smul_neg, sub_neg_eq_add, ← add_smul]
    norm_num
  have hw : (fun p => (x2hWeight p : ℂ)) = fun p => (1 / 96 : ℂ) * (x2hNum p : ℂ) := by
    funext p
    unfold x2hWeight x2hDen
    push_cast
    ring
  rw [x2hCarrier_rho, hw, x2hRho_cmul, Matrix.smul_mul, hE, smul_smul]
  norm_num

/-- `carrier_fix` (mirror form) for an h key from its three transposition identities. -/
theorem x2hCarrierFix (b : x2Key 0)
    (h12 : rhoG (x2hTau b) (x2hSpecial 5) * x2hImage b = -x2hImage b)
    (h34 : rhoG (x2hTau b) (x2hSpecial 10) * x2hImage b = -x2hImage b)
    (hT : (∑ u : Fin 10, rhoG (x2hTau b) (x2hSpecial u.succ.castSucc)) * x2hImage b = (2 : ℂ) • x2hImage b) :
    x2hCarrier (x2hTau b) * x2hImage b = x2hImage b :=
  x2hCarrierFix_of_transp (x2hTau b) (x2hImage b) h12 h34 hT

end ThreeCopyQutritWerner.X2Sites
