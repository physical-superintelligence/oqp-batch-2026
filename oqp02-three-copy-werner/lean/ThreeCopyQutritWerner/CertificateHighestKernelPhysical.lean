module

public import ThreeCopyQutritWerner.CertificateWeightSpaces
public import ThreeCopyQutritWerner.CertificateKernelFrame

@[expose] public section


/-!
# From finite highest-kernel checks to the actual physical source action

The finite reconstruction is applied only after proving that a physical highest
vector is supported on the exhaustive input rows and is killed by the selected
physical raising tests. The result is lifted back to every physical coordinate.
Thus generator commutation determines the source-frame action; no source action
or highest-weight multiplicity theorem is an additional assumption.
-/

noncomputable section

open scoped BigOperators Matrix ComplexOrder

namespace ThreeCopyQutritWerner

/-- Integer weight and raising equations give the literal complex highest columns. -/
theorem certificateIntFrame_columns_highest {m : Type*} [Fintype m]
    (ket : Finset (Fin 6)) (lam : Fin 3 → ℤ)
    (U : Matrix CertificateLocalWord m ℤ)
    (hweight : ∀ w j i, certificateLocalWeight ket w i * U w j = lam i * U w j)
    (h01 : certificateLocalGenerator ket 0 1 * U = 0)
    (h12 : certificateLocalGenerator ket 1 2 * U = 0) (j : m) :
    certificateIsHighest ket lam (fun w => (U w j : ℂ)) := by
  refine ⟨?_, ?_, ?_⟩
  · apply (certificateHasWeight_iff_cartan ket lam _).mpr
    intro i
    rw [certificateLocalGenerator_cartan_complex]
    ext w
    have h := congrArg (Int.cast : ℤ → ℂ) (hweight w j i)
    simpa [Matrix.mulVec, dotProduct, Matrix.diagonal_apply, Pi.smul_apply,
      smul_eq_mul] using h
  · ext w
    have h := congrArg (Int.cast : ℤ → ℂ) (congrFun (congrFun h01 w) j)
    simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply] using h
  · ext w
    have h := congrArg (Int.cast : ℤ → ℂ) (congrFun (congrFun h12 w) j)
    simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply] using h

/-- Map the exact scaled integer reconstruction to complex arithmetic. -/
theorem certificateIntKernel_reconstruction_complex {n m q : Type*}
    [Fintype n] [Fintype m] [Fintype q] [DecidableEq n]
    (U : Matrix n m ℤ) (P : Matrix m n ℤ) (R : Matrix q n ℤ) (W : Matrix n q ℤ)
    (d : ℤ) (h : d • (1 - U * P) = W * R) :
    (d : ℂ) • (1 - U.map (Int.cast : ℤ → ℂ) * P.map (Int.cast : ℤ → ℂ)) =
      W.map (Int.cast : ℤ → ℂ) * R.map (Int.cast : ℤ → ℂ) := by
  ext i j
  have he := congrArg (Int.cast : ℤ → ℂ) (congrFun (congrFun h i) j)
  simpa [Matrix.mul_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul] using he

/-- Every highest vector is reconstructed by the original physical frame, with
its coefficient vector given by the checked finite pivot projection. -/
theorem certificateHighestPhysical_reconstruct {n m q : Type*}
    [Fintype n] [Fintype m] [Fintype q] [DecidableEq n]
    (ket : Finset (Fin 6)) (lam : Fin 3 → ℤ)
    (F : Matrix CertificateLocalWord m ℤ)
    (hF : ∀ j, certificateIsHighest ket lam (fun w => (F w j : ℂ)))
    (row : n → CertificateLocalWord) (hrow : Function.Injective row)
    (hcover : ∀ w, certificateLocalWeight ket w = lam → ∃ i, row i = w)
    (test : q → Fin 2 × CertificateLocalWord)
    (U : Matrix n m ℤ) (P : Matrix m n ℤ) (R : Matrix q n ℤ) (W : Matrix n q ℤ)
    (hU : F.submatrix row id = U)
    (hR : R = certificateRestrictedRaising ket row test)
    (d : ℤ) (hd : d ≠ 0) (hcert : d • (1 - U * P) = W * R)
    (v : CertificateLocalWord → ℂ) (hv : certificateIsHighest ket lam v) :
    v = F.map (Int.cast : ℤ → ℂ) *ᵥ (P.map (Int.cast : ℤ → ℂ) *ᵥ (v ∘ row)) := by
  have hkill : R.map (Int.cast : ℤ → ℂ) *ᵥ (v ∘ row) = 0 := by
    rw [hR]
    exact certificateRestrictedRaising_kills ket lam row hrow hcover test v hv
  have hdc : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  have hfinite := certificate_kernelFrame_reconstruct_vector
    (U.map (Int.cast : ℤ → ℂ)) (P.map (Int.cast : ℤ → ℂ))
    (R.map (Int.cast : ℤ → ℂ)) (W.map (Int.cast : ℤ → ℂ))
    (d : ℂ) hdc (certificateIntKernel_reconstruction_complex U P R W d hcert)
    (v ∘ row) hkill
  rw [← hU] at hfinite
  ext w
  by_cases hw : certificateLocalWeight ket w = lam
  · obtain ⟨i, rfl⟩ := hcover w hw
    exact congrFun hfinite i
  · rw [hv.1 w hw]
    symm
    apply Finset.sum_eq_zero
    intro j _
    exact mul_eq_zero_of_left ((hF j).1 w hw) _

/-- Reconstruction of the preserved highest columns proves the full physical action. -/
theorem certificateHighestPhysical_source_action {n m : Type*}
    [Fintype n] [Fintype m]
    (ket : Finset (Fin 6)) (lam : Fin 3 → ℤ)
    (F : Matrix CertificateLocalWord m ℂ) (row : n → CertificateLocalWord)
    (P : Matrix m n ℂ)
    (hF : ∀ j, certificateIsHighest ket lam (fun w => F w j))
    (hreconstruct : ∀ v, certificateIsHighest ket lam v →
      v = F *ᵥ (P *ᵥ (v ∘ row)))
    (M : Matrix CertificateLocalWord CertificateLocalWord ℂ)
    (hcomm : ∀ i j : Fin 3,
      M * (certificateLocalGenerator ket i j).map (Int.cast : ℤ → ℂ) =
        (certificateLocalGenerator ket i j).map (Int.cast : ℤ → ℂ) * M) :
    M * F = F * (P * (M * F).submatrix row id) := by
  ext w j
  have hh := certificateIsHighest_mulVec ket lam M hcomm (fun w => F w j) (hF j)
  exact congrFun (hreconstruct (M *ᵥ fun w => F w j) hh) w

/-- A linear combination of actual highest columns is still a physical highest vector. -/
theorem certificateHighestPhysical_mulVec {m : Type*} [Fintype m]
    (ket : Finset (Fin 6)) (lam : Fin 3 → ℤ)
    (F : Matrix CertificateLocalWord m ℂ)
    (hF : ∀ j, certificateIsHighest ket lam (fun w => F w j)) (a : m → ℂ) :
    certificateIsHighest ket lam (F *ᵥ a) := by
  refine ⟨?_, ?_, ?_⟩
  · intro w hw
    apply Finset.sum_eq_zero
    intro j _
    exact mul_eq_zero_of_left ((hF j).1 w hw) _
  · have h01 : (certificateLocalGenerator ket 0 1).map (Int.cast : ℤ → ℂ) * F = 0 := by
      ext w j
      exact congrFun (hF j).2.1 w
    rw [Matrix.mulVec_mulVec, h01, Matrix.zero_mulVec]
  · have h12 : (certificateLocalGenerator ket 1 2).map (Int.cast : ℤ → ℂ) * F = 0 := by
      ext w j
      exact congrFun (hF j).2.2 w
    rw [Matrix.mulVec_mulVec, h12, Matrix.zero_mulVec]

/-- In the original positive metric, any recovered action is exactly G⁻¹ times
the literal physical compression. The auxiliary coefficient matrix disappears. -/
theorem certificateHighestPhysical_weighted_action {m : Type*}
    [Fintype m] [DecidableEq m]
    (F : Matrix CertificateLocalWord m ℂ)
    (M : Matrix CertificateLocalWord CertificateLocalWord ℂ)
    (A : Matrix m m ℂ) (hact : M * F = F * A) (hG : (Fᴴ * F).PosDef) :
    M * F = F * ((Fᴴ * F)⁻¹ * (Fᴴ * M * F)) := by
  have hcomp : Fᴴ * M * F = (Fᴴ * F) * A := by
    rw [Matrix.mul_assoc, hact, ← Matrix.mul_assoc]
  rw [hcomp, Matrix.nonsing_inv_mul_cancel_left _ _
    ((Matrix.isUnit_iff_isUnit_det _).mp hG.isUnit)]
  exact hact

end ThreeCopyQutritWerner
