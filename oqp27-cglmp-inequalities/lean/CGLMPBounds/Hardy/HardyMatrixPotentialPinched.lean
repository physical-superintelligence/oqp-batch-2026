module

public import CGLMPBounds.Hardy.HardyMatrixPotentialContinuity
public import CGLMPBounds.Hardy.HermitianPairDiagonalization
public import CGLMPBounds.Hardy.PositivePinchingUnitary

@[expose] public section


/-! At an actual commuting Hermitian involution plus iC, the boundary
potential is exactly the normalized trace of the actual matrix absolute
value of C. Joint diagonalization retains every multiplicity. -/

namespace CGLMPBounds.Hardy
noncomputable section
open Matrix Unitary
open scoped Matrix.Norms.L2Operator MatrixOrder
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma normalizedMatrixAbsTrace_eq_root_sum {C : Matrix ι ι ℂ} (hC : C.IsHermitian) :
    normalizedMatrixAbsTrace C =
      (C.charpoly.roots.map (fun z : ℂ => |z.re|)).sum / (Fintype.card ι : ℝ) := by
  unfold normalizedMatrixAbsTrace
  rw [CFC.abs_eq_cfc_norm C hC, hC.cfc_eq, Matrix.IsHermitian.cfc,
    trace_conjStarAlgAut, Matrix.trace_diagonal, hC.roots_charpoly_eq_eigenvalues]
  simp only [Function.comp_def, Complex.re_sum, Complex.ofReal_re,
    Real.norm_eq_abs, Multiset.map_map]
  rfl

lemma charpoly_unitary_diagonal {U : Matrix ι ι ℂ} (hU : Uᴴ*U=1)
    (v : ι → ℂ) :
    (U*Matrix.diagonal v*Uᴴ).charpoly=rootVectorPolynomial v := by
  rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul,
    Matrix.charpoly_diagonal]
  rfl

theorem matrixHardyPotential_commuting_boundary {B C : Matrix ι ι ℂ}
    (hB : B.IsHermitian) (hB2 : B^2=1) (hC : C.IsHermitian) (hBC : B*C=C*B) :
    matrixHardyPotential (B+Complex.I • C)=normalizedMatrixAbsTrace C := by
  obtain ⟨U,b,c,hU,hU',hBd,hCd⟩ := hermitian_pair_unitary_diagonalization hB hC hBC
  have hdiag : Uᴴ*B*U=Matrix.diagonal (fun i => (b i : ℂ)) := by
    rw [hBd]
    calc
      _=(Uᴴ*U)*Matrix.diagonal (fun i => (b i : ℂ))*(Uᴴ*U) := by noncomm_ring
      _=_ := by rw [hU]; simp
  have hsq : (Matrix.diagonal (fun i => (b i : ℂ)))^2=1 := by
    rw [← hdiag]
    calc
      (Uᴴ*B*U)^2=Uᴴ*B*(U*Uᴴ)*B*U := by noncomm_ring
      _=Uᴴ*B^2*U := by rw [hU']; simp only [Matrix.mul_one, pow_two, Matrix.mul_assoc]
      _=1 := by rw [hB2]; simpa only [Matrix.mul_one] using hU
  have hsign (i : ι) : b i=1 ∨ b i=-1 := by
    have hi := congrArg (fun A : Matrix ι ι ℂ => A i i) hsq
    simp only [pow_two, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq,
      Matrix.one_apply_eq] at hi
    have hb : (b i)^2=1 := by exact_mod_cast (show (b i : ℂ)^2=1 by simpa only [pow_two] using hi)
    exact (sq_eq_one_iff).mp hb
  have hAd : B+Complex.I • C=
      U*Matrix.diagonal (fun i => (b i : ℂ)+Complex.I*(c i : ℂ))*Uᴴ := by
    rw [hBd,hCd]
    have hd : Matrix.diagonal (fun i => (b i : ℂ)+Complex.I*(c i : ℂ))=
        Matrix.diagonal (fun i => (b i : ℂ))+Complex.I • Matrix.diagonal (fun i => (c i : ℂ)) := by
      ext i j
      by_cases hij : i=j
      · subst j
        simp
      · simp [Matrix.diagonal_apply, hij]
    rw [hd, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  rw [matrixHardyPotential_eq_root_sum,
    root_sum_eq_vector_sum_of_factorization _ _ (by rw [hAd]; exact charpoly_unitary_diagonal hU _),
    normalizedMatrixAbsTrace_eq_root_sum hC,
    root_sum_eq_vector_sum_of_factorization _ _ (by rw [hCd]; exact charpoly_unitary_diagonal hU _)]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  change (hardyStripPotential ((b i : ℂ)+Complex.I*(c i : ℂ))).re=|(c i : ℂ).re|
  rw [Complex.ofReal_re]
  rcases hsign i with hb | hb
  · simpa only [hb, Complex.ofReal_one, hardyStripRealPotential] using
      (hardyStripRealPotential_boundary (c i)).1
  · simpa only [hb, Complex.ofReal_neg, Complex.ofReal_one, hardyStripRealPotential] using
      (hardyStripRealPotential_boundary (c i)).2

theorem matrixHardyPotential_pinched_boundary {B Y : Matrix ι ι ℂ}
    (hB : B.IsHermitian) (hB2 : B^2=1) (hY : Y.IsHermitian) :
    matrixHardyPotential (B+Complex.I • positivePinchingPart B Y)=
      normalizedMatrixAbsTrace (positivePinchingPart B Y) :=
  matrixHardyPotential_commuting_boundary hB hB2 (positivePinching_part_hermitian hB hY)
    (positivePinching_part_commute hB2)

end
end CGLMPBounds.Hardy
