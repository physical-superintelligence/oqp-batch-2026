module

public import CGLMPBounds.Hardy.HardyMatrixPotentialPinched
public import CGLMPBounds.Quantum.HermitianTraceVariation
public import CGLMPBounds.Quantum.UnitaryCompact
public import CGLMPBounds.Circulation.Core

@[expose] public section


/-! Pointwise trace bound in C.16, for actual commuting Hermitian
involutions. The absolute value is CFC.abs, not an assumed norm bound. -/
namespace CGLMPBounds.Hardy
open Matrix
noncomputable section

 theorem normalizedMatrixAbsTrace_eigenvalues {r : ℕ} {X : Circulation.Mat r}
    (hX : X.IsHermitian) :
    normalizedMatrixAbsTrace X = (∑ i, |hX.eigenvalues i|)/(r : ℝ) := by
  rw [normalizedMatrixAbsTrace_eq_root_sum hX, hX.roots_charpoly_eq_eigenvalues]
  simp only [Multiset.map_map, Function.comp_apply, RCLike.ofReal_eq_complex_ofReal,
    Complex.ofReal_re, Fintype.card_fin]
  <;> rfl

theorem reTr_unitary_mul_le_absTrace {r : ℕ} (A C : Circulation.Mat r)
    (hA : Aᴴ*A=1) (hC : C.IsHermitian) :
    Circulation.reTr (A*C) ≤ normalizedMatrixAbsTrace C := by
  let V := hC.eigenvectorUnitary
  let UA : Matrix.unitaryGroup (Fin r) ℂ := ⟨A, Matrix.mem_unitaryGroup_iff'.mpr hA⟩
  let D : Matrix.unitaryGroup (Fin r) ℂ := star V * UA * V
  have hdiag (i : Fin r) : |(((V : Circulation.Mat r)ᴴ*A*V) i i).re| ≤ 1 := by
    exact (Complex.abs_re_le_norm _).trans (unitary_entry_norm_le_one D i i)
  rw [Circulation.reTr_eq, Matrix.trace_mul_comm A C,
    re_trace_mul_in_eigenbasis hC, normalizedMatrixAbsTrace_eigenvalues hC]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg r)
  apply Finset.sum_le_sum
  intro i _
  calc
    _ ≤ |hC.eigenvalues i * (((V : Circulation.Mat r)ᴴ*A*V) i i).re| := le_abs_self _
    _ = |hC.eigenvalues i| * |(((V : Circulation.Mat r)ᴴ*A*V) i i).re| := abs_mul _ _
    _ ≤ |hC.eigenvalues i| * 1 := mul_le_mul_of_nonneg_left (hdiag i) (abs_nonneg _)
    _ = _ := mul_one _

theorem reTr_commuting_pinching {r : ℕ} (A B Y : Circulation.Mat r)
    (hB2 : B^2=1) (hAB : A*B=B*A) :
    Circulation.reTr (A*positivePinchingPart B Y) = Circulation.reTr (A*Y) := by
  have hBB : B*B=1 := by simpa only [pow_two] using hB2
  have hBAB : B*A*B=A := by rw [← hAB, Matrix.mul_assoc, hBB, Matrix.mul_one]
  have heq : Matrix.trace (A*(B*Y*B)) = Matrix.trace (A*Y) := by
    calc
      _ = Matrix.trace ((A*B*Y)*B) := by simp only [Matrix.mul_assoc]
      _ = Matrix.trace (B*(A*B*Y)) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace ((B*A*B)*Y) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hBAB]
  simp only [positivePinchingPart, Matrix.mul_smul, Matrix.mul_add, Circulation.reTr_eq,
    Matrix.trace_smul, Matrix.trace_add, heq]
  norm_num [Complex.smul_re, smul_eq_mul, Complex.mul_re]
  <;> ring

theorem hermitian_involution_pinching_trace_bound {r : ℕ} (A B Y : Circulation.Mat r)
    (hA : A.IsHermitian) (hA2 : A^2=1) (hB : B.IsHermitian) (hB2 : B^2=1)
    (hY : Y.IsHermitian) (hAB : A*B=B*A) :
    Circulation.reTr (A*Y) ≤ normalizedMatrixAbsTrace (positivePinchingPart B Y) := by
  rw [← reTr_commuting_pinching A B Y hB2 hAB]
  apply reTr_unitary_mul_le_absTrace
  · rw [hA.eq, ← pow_two, hA2]
  · exact positivePinching_part_hermitian hB hY

end
end CGLMPBounds.Hardy
