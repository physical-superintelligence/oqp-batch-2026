module

public import CGLMPBounds.Defs.DeficitHSSq

@[expose] public section


/-!
# The factor-two PVM conjugation estimate

Appendix E, proof of Theorem A.2: for any PVM `(P_a)` and unitaries `U,V`,
`∑ₐ ‖UPₐU* - VPₐV*‖²_F ≤ 2 ‖U-V‖²_F`.
The proof is the exact pinching identity
`∑ₐ ‖PₐX-XPₐ‖²_F = 2‖X‖²_F - 2∑ₐ ‖PₐXPₐ‖²_F`,
applied to `X=U*V-I`. No rank-one or equal-rank assumption is imposed.
-/

open Matrix
open scoped ComplexOrder

namespace CGLMPBounds

noncomputable section

variable {n : ℕ}

theorem deficitHSSq_nonneg (X : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ deficitHSSq X :=
  (Complex.nonneg_iff.mp (Matrix.posSemidef_conjTranspose_mul_self X).trace_nonneg).1

theorem deficitHSSq_sub (X Y : Matrix (Fin n) (Fin n) ℂ) :
    deficitHSSq (X - Y) = deficitHSSq X + deficitHSSq Y
      - 2 * (Matrix.trace (Xᴴ * Y)).re := by
  have hcross : (Matrix.trace (Yᴴ * X)).re = (Matrix.trace (Xᴴ * Y)).re := by
    simpa using congrArg Complex.re (Matrix.trace_conjTranspose (Xᴴ * Y))
  unfold deficitHSSq
  rw [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
    Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_sub]
  simp only [Complex.sub_re]
  rw [hcross]
  ring

theorem deficitHSSq_sub_comm (X Y : Matrix (Fin n) (Fin n) ℂ) :
    deficitHSSq (X - Y) = deficitHSSq (Y - X) := by
  have hcross : (Matrix.trace (Yᴴ * X)).re = (Matrix.trace (Xᴴ * Y)).re := by
    simpa using congrArg Complex.re (Matrix.trace_conjTranspose (Xᴴ * Y))
  rw [deficitHSSq_sub, deficitHSSq_sub, hcross]
  ring

theorem deficitHSSq_projection_left {P : Matrix (Fin n) (Fin n) ℂ}
    (hP : P.IsHermitian) (hP2 : P * P = P) (X : Matrix (Fin n) (Fin n) ℂ) :
    deficitHSSq (P * X) = (Matrix.trace (Xᴴ * P * X)).re := by
  simp only [deficitHSSq, Matrix.conjTranspose_mul, hP.eq, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc P P, hP2]

theorem deficitHSSq_projection_right {P : Matrix (Fin n) (Fin n) ℂ}
    (hP : P.IsHermitian) (hP2 : P * P = P) (X : Matrix (Fin n) (Fin n) ℂ) :
    deficitHSSq (X * P) = (Matrix.trace (Xᴴ * X * P)).re := by
  simp only [deficitHSSq, Matrix.conjTranspose_mul, hP.eq, Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm P]
  simp only [Matrix.mul_assoc, hP2]

theorem deficitHSSq_projection_sandwich {P : Matrix (Fin n) (Fin n) ℂ}
    (hP : P.IsHermitian) (hP2 : P * P = P) (X : Matrix (Fin n) (Fin n) ℂ) :
    deficitHSSq (P * X * P) = (Matrix.trace (Xᴴ * P * X * P)).re := by
  simp only [deficitHSSq, Matrix.conjTranspose_mul, hP.eq, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc P P, hP2, Matrix.trace_mul_comm P]
  simp only [Matrix.mul_assoc, hP2]

variable {α : Type*} [Fintype α]

theorem sum_deficitHSSq_projection_left {P : α → Matrix (Fin n) (Fin n) ℂ}
    (hP : IsPVM P) (X : Matrix (Fin n) (Fin n) ℂ) :
    ∑ a, deficitHSSq (P a * X) = deficitHSSq X := by
  simp_rw [deficitHSSq_projection_left (hP.isHermitian _) (hP.mul_self _)]
  rw [← Complex.re_sum, ← Matrix.trace_sum, ← Finset.sum_mul, ← Finset.mul_sum,
    hP.sum_eq_one, Matrix.mul_one]
  rfl

theorem sum_deficitHSSq_projection_right {P : α → Matrix (Fin n) (Fin n) ℂ}
    (hP : IsPVM P) (X : Matrix (Fin n) (Fin n) ℂ) :
    ∑ a, deficitHSSq (X * P a) = deficitHSSq X := by
  simp_rw [deficitHSSq_projection_right (hP.isHermitian _) (hP.mul_self _)]
  rw [← Complex.re_sum, ← Matrix.trace_sum, ← Finset.mul_sum, hP.sum_eq_one,
    Matrix.mul_one]
  rfl

/-- Exact Hilbert–Schmidt pinching identity for a PVM. -/
theorem sum_deficitHSSq_commutator {P : α → Matrix (Fin n) (Fin n) ℂ}
    (hP : IsPVM P) (X : Matrix (Fin n) (Fin n) ℂ) :
    ∑ a, deficitHSSq (P a * X - X * P a)
      = 2 * deficitHSSq X - 2 * ∑ a, deficitHSSq (P a * X * P a) := by
  have hcross : ∀ a, (Matrix.trace ((P a * X)ᴴ * (X * P a))).re
      = deficitHSSq (P a * X * P a) := by
    intro a
    rw [deficitHSSq_projection_sandwich (hP.isHermitian a) (hP.mul_self a),
      Matrix.conjTranspose_mul, (hP.isHermitian a).eq]
    simp only [Matrix.mul_assoc]
  simp_rw [deficitHSSq_sub, hcross]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    sum_deficitHSSq_projection_left hP, sum_deficitHSSq_projection_right hP]
  ring

theorem sum_deficitHSSq_commutator_le {P : α → Matrix (Fin n) (Fin n) ℂ}
    (hP : IsPVM P) (X : Matrix (Fin n) (Fin n) ℂ) :
    ∑ a, deficitHSSq (P a * X - X * P a) ≤ 2 * deficitHSSq X := by
  rw [sum_deficitHSSq_commutator hP]
  exact sub_le_self _ (mul_nonneg (by norm_num)
    (Finset.sum_nonneg (fun a _ => deficitHSSq_nonneg (P a * X * P a))))

theorem deficitHSSq_unitary_left {U : Matrix (Fin n) (Fin n) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    deficitHSSq (U * X) = deficitHSSq X := by
  have hUU : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  unfold deficitHSSq
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ U,
    hUU, Matrix.one_mul]

theorem deficitHSSq_unitary_right {U : Matrix (Fin n) (Fin n) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    deficitHSSq (X * U) = deficitHSSq X := by
  have hUU : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  unfold deficitHSSq
  rw [Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm Uᴴ]
  simp only [Matrix.mul_assoc, hUU, Matrix.mul_one]

/-- Source's factor-two estimate, with unitary matrices as elements of the unitary group. -/
theorem pvm_conjugation_distance_le (U V : Matrix.unitaryGroup (Fin n) ℂ)
    {P : α → Matrix (Fin n) (Fin n) ℂ} (hP : IsPVM P) :
    ∑ a, deficitHSSq ((U : Matrix (Fin n) (Fin n) ℂ) * P a * star (U : Matrix (Fin n) (Fin n) ℂ)
      - (V : Matrix (Fin n) (Fin n) ℂ) * P a * star (V : Matrix (Fin n) (Fin n) ℂ))
      ≤ 2 * deficitHSSq ((U : Matrix (Fin n) (Fin n) ℂ) - (V : Matrix (Fin n) (Fin n) ℂ)) := by
  let W : Matrix (Fin n) (Fin n) ℂ := star (U : Matrix (Fin n) (Fin n) ℂ) * V
  have hUU : (U : Matrix (Fin n) (Fin n) ℂ) * star (U : Matrix (Fin n) (Fin n) ℂ) = 1 :=
    Unitary.coe_mul_star_self U
  have hVV : (V : Matrix (Fin n) (Fin n) ℂ) * star (V : Matrix (Fin n) (Fin n) ℂ) = 1 :=
    Unitary.coe_mul_star_self V
  have hVstar : star (V : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ :=
    Unitary.star_mem V.property
  have hconj : ∀ a, deficitHSSq ((U : Matrix (Fin n) (Fin n) ℂ) * P a * star (U : Matrix (Fin n) (Fin n) ℂ)
        - (V : Matrix (Fin n) (Fin n) ℂ) * P a * star (V : Matrix (Fin n) (Fin n) ℂ))
      = deficitHSSq (P a * W - W * P a) := by
    intro a
    have heq : (U : Matrix (Fin n) (Fin n) ℂ) * (P a * W - W * P a)
        * star (V : Matrix (Fin n) (Fin n) ℂ)
        = (U : Matrix (Fin n) (Fin n) ℂ) * P a * star (U : Matrix (Fin n) (Fin n) ℂ)
          - (V : Matrix (Fin n) (Fin n) ℂ) * P a * star (V : Matrix (Fin n) (Fin n) ℂ) := by
      simp only [W, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
      rw [hVV, Matrix.mul_one, ← Matrix.mul_assoc (U : Matrix (Fin n) (Fin n) ℂ)
        (star (U : Matrix (Fin n) (Fin n) ℂ)), hUU, Matrix.one_mul]
    rw [← heq, deficitHSSq_unitary_right hVstar,
      deficitHSSq_unitary_left U.property]
  have hdelta : deficitHSSq (W - 1)
      = deficitHSSq ((U : Matrix (Fin n) (Fin n) ℂ) - (V : Matrix (Fin n) (Fin n) ℂ)) := by
    have heq : (U : Matrix (Fin n) (Fin n) ℂ) * (W - 1)
        = (V : Matrix (Fin n) (Fin n) ℂ) - (U : Matrix (Fin n) (Fin n) ℂ) := by
      dsimp only [W]
      rw [Matrix.mul_sub, ← Matrix.mul_assoc, hUU, Matrix.one_mul, Matrix.mul_one]
    rw [← deficitHSSq_unitary_left U.property (W - 1), heq, deficitHSSq_sub_comm]
  have hcomm : ∀ a, P a * (W - 1) - (W - 1) * P a = P a * W - W * P a := by
    intro a
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul]
    abel
  have h := sum_deficitHSSq_commutator_le hP (W - 1)
  simpa only [hconj, hcomm, hdelta] using h

end

end CGLMPBounds
