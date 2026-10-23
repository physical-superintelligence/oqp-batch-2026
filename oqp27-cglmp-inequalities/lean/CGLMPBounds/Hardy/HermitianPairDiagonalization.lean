module

public import Mathlib.Analysis.InnerProductSpace.JointEigenspace
public import Mathlib.Analysis.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.Analysis.InnerProductSpace.Spectrum

@[expose] public section


/-! Actual simultaneous unitary diagonalization of two commuting Hermitian
matrices, from Mathlib's complete orthogonal joint-eigenspace decomposition.
No eigenbasis is supplied as a hypothesis. -/

namespace CGLMPBounds.Hardy
noncomputable section
open Matrix
open scoped ComplexConjugate
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem hermitian_pair_unitary_diagonalization {B C : Matrix ι ι ℂ}
    (hB : B.IsHermitian) (hC : C.IsHermitian) (hBC : B*C=C*B) :
    ∃ (U : Matrix ι ι ℂ) (b c : ι → ℝ),
      Uᴴ*U=1 ∧ U*Uᴴ=1 ∧
      B=U*Matrix.diagonal (fun i => (b i : ℂ))*Uᴴ ∧
      C=U*Matrix.diagonal (fun i => (c i : ℂ))*Uᴴ := by
  classical
  let A : Bool → Matrix ι ι ℂ := fun s => if s then C else B
  let J : (Bool → ℂ) → Submodule ℂ (EuclideanSpace ℂ ι) :=
    fun χ => ⨅ s, Module.End.eigenspace (A s).toEuclideanLin (χ s)
  have hsym (s : Bool) : (A s).toEuclideanLin.IsSymmetric := by
    apply Matrix.isSymmetric_toEuclideanLin_iff.mpr
    cases s <;> simp only [A, Bool.false_eq_true, if_false, if_true] <;> assumption
  have horth : OrthogonalFamily ℂ (fun χ => J χ) (fun χ => (J χ).subtypeₗᵢ) :=
    LinearMap.IsSymmetric.orthogonalFamily_iInf_eigenspaces hsym
  have hspan : (⨆ χ, J χ) = ⊤ := by
    apply LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hsym
    intro s t _
    have hc : A s*A t=A t*A s := by cases s <;> cases t <;> simp [A, hBC]
    change (A s).toEuclideanLin*(A t).toEuclideanLin =
      (A t).toEuclideanLin*(A s).toEuclideanLin
    simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same, Module.End.mul_eq_comp]
      using congrArg (Matrix.toLpLin 2 2) hc
  have hint : DirectSum.IsInternal J := horth.isInternal_iff.mpr (by
    rw [hspan, Submodule.top_orthogonal_eq_bot])
  let I := {χ : Bool → ℂ // J χ ≠ ⊥}
  letI : Fintype I := hint.submodule_iSupIndep.fintypeNeBotOfFiniteDimensional
  let J' : I → Submodule ℂ (EuclideanSpace ℂ ι) := fun χ => J χ.val
  have horth' : OrthogonalFamily ℂ (fun χ => J' χ) (fun χ => (J' χ).subtypeₗᵢ) := by
    intro i j hij v w
    exact horth (Subtype.val_injective.ne hij) v w
  have hspan' : (⨆ χ : I, J' χ) = ⊤ := by
    apply top_unique
    rw [← hspan]
    apply iSup_le
    intro χ
    by_cases hχ : J χ = ⊥
    · simp only [hχ, bot_le]
    · exact le_iSup J' (⟨χ, hχ⟩ : I)
  have hint' : DirectSum.IsInternal J' := horth'.isInternal_iff.mpr (by
    rw [hspan', Submodule.top_orthogonal_eq_bot])
  have hdim : Module.finrank ℂ (EuclideanSpace ℂ ι)=Fintype.card ι := by simp
  let e := Fintype.equivFin ι
  let b₀ := hint'.subordinateOrthonormalBasis hdim horth'
  let b := b₀.reindex e.symm
  let χ (i : ι) := (hint'.subordinateOrthonormalBasisIndex hdim (e i) horth').val
  have hb (i : ι) : b i ∈ J (χ i) := by
    simpa only [b, OrthonormalBasis.reindex_apply, Equiv.symm_symm] using
      hint'.subordinateOrthonormalBasis_subordinate hdim (e i) horth'
  have hbn (i : ι) : b i ≠ 0 := by
    intro he
    have hn := b.orthonormal.1 i
    rw [he, norm_zero] at hn
    exact zero_ne_one hn
  have he (i : ι) (s : Bool) : (A s).toEuclideanLin (b i)=χ i s • b i :=
    Module.End.mem_eigenspace_iff.mp (((Submodule.mem_iInf _).mp (hb i)) s)
  have hreal (i : ι) (s : Bool) : ((χ i s).re : ℂ)=χ i s := by
    have hc := (hsym s).conj_eigenvalue_eq_self
      (Module.End.hasEigenvalue_of_hasEigenvector
        ⟨Module.End.mem_eigenspace_iff.mpr (he i s), hbn i⟩)
    have him : (χ i s).im=0 := by
      have hi := congrArg Complex.im hc
      simp only [Complex.conj_im] at hi
      linarith
    exact Complex.ext rfl (by simpa only [Complex.ofReal_im] using him.symm)
  let U : Matrix ι ι ℂ := (EuclideanSpace.basisFun ι ℂ).toBasis.toMatrix b
  have hU : Uᴴ*U=1 :=
    (EuclideanSpace.basisFun ι ℂ).toMatrix_orthonormalBasis_conjTranspose_mul_self b
  have hU' : U*Uᴴ=1 :=
    (EuclideanSpace.basisFun ι ℂ).toMatrix_orthonormalBasis_self_mul_conjTranspose b
  have hUentry (i k : ι) : U i k = (b k) i := by
    simp only [U, Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      EuclideanSpace.basisFun_repr]
  have hd (s : Bool) : A s=U*Matrix.diagonal (fun i => ((χ i s).re : ℂ))*Uᴴ := by
    have ha : A s*U=U*Matrix.diagonal (fun i => ((χ i s).re : ℂ)) := by
      ext i k
      rw [Matrix.mul_apply, Matrix.mul_diagonal, hreal]
      have hi := congrArg (fun v : EuclideanSpace ℂ ι => v i) (he k s)
      change (∑ q, A s i q * (b k) q)=χ k s*(b k) i at hi
      simpa only [hUentry, mul_comm] using hi
    calc
      _ = A s*(U*Uᴴ) := by rw [hU', Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, ha]
  exact ⟨U, (fun i => (χ i false).re), (fun i => (χ i true).re), hU, hU',
    by simpa only [A, Bool.false_eq_true, if_false] using hd false,
    by simpa only [A, if_true] using hd true⟩

end
end CGLMPBounds.Hardy
