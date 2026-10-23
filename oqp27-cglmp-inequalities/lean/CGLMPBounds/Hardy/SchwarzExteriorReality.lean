module

public import CGLMPBounds.Hardy.SchwarzExteriorContour

@[expose] public section


/-!
# Reality of the actual exterior cluster trace on a real neighborhood

The Hermitian spectral theorem for Y proves `I-wY` positive definite for real
w near zero. The existing quadratic-form pencil argument then makes every
root of `H⁻¹(I-wY)` real, including defective or repeated roots. The literal
contour definition of q is therefore real on this neighborhood.

This supplies the reality premise in the source p. 8 construction without an
assumed similarity, continuously enumerated eigenvalues or real-coefficient
oracle. Real Taylor coefficients and the exterior g/q identity remain separate.
-/

open Complex Metric Set Filter Matrix Unitary
open scoped Topology Interval Matrix.Norms.Operator ComplexOrder

namespace CGLMPBounds.Hardy
noncomputable section

lemma multiset_sum_im_eq_zero (s : Multiset ℂ) (hs : ∀ a ∈ s, a.im = 0) :
    s.sum.im = 0 := by
  revert hs
  induction s using Multiset.induction_on with
  | empty => intro _; simp
  | @cons a s ih =>
    intro hs
    rw [Multiset.sum_cons, Complex.add_im,
      hs a (Multiset.mem_cons_self _ _),
      ih (fun b hb => hs b (Multiset.mem_cons_of_mem hb)), zero_add]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

lemma one_sub_real_smul_spectral {Y : Matrix ι ι ℂ}
    (hY : Y.IsHermitian) (w : ℝ) :
    (1 : Matrix ι ι ℂ) - (w : ℂ) • Y =
      conjStarAlgAut ℂ _ hY.eigenvectorUnitary
        (Matrix.diagonal fun i => ((1 - w * hY.eigenvalues i : ℝ) : ℂ)) := by
  have hd : (Matrix.diagonal fun i => ((1 - w * hY.eigenvalues i : ℝ) : ℂ)) =
      (1 : Matrix ι ι ℂ) -
        (w : ℂ) • Matrix.diagonal (fun i => (hY.eigenvalues i : ℂ)) := by
    ext i j
    by_cases h : i = j
    · subst j
      simp [Matrix.diagonal_apply, Matrix.one_apply]
    · simp [Matrix.diagonal_apply, Matrix.one_apply, h]
  rw [hd, map_sub, map_one, map_smul]
  change (1 : Matrix ι ι ℂ) - (w : ℂ) • Y =
    1 - (w : ℂ) • conjStarAlgAut ℂ _ hY.eigenvectorUnitary
      (Matrix.diagonal (RCLike.ofReal ∘ hY.eigenvalues))
  rw [← hY.spectral_theorem]

lemma one_sub_real_smul_posDef {Y : Matrix ι ι ℂ}
    (hY : Y.IsHermitian) (w : ℝ)
    (hw : ∀ i, 0 < 1 - w * hY.eigenvalues i) :
    ((1 : Matrix ι ι ℂ) - (w : ℂ) • Y).PosDef := by
  rw [one_sub_real_smul_spectral hY w, conjStarAlgAut_apply]
  apply (Unitary.isUnit_coe (U := hY.eigenvectorUnitary)).posDef_star_right_conjugate_iff.mpr
  rw [Matrix.posDef_diagonal_iff]
  intro i
  exact_mod_cast hw i

/-- Positivity follows from finitely many continuous affine eigenvalue
expressions, and is not an extra hypothesis on the exterior construction. -/
theorem eventually_one_sub_real_smul_posDef {Y : Matrix ι ι ℂ}
    (hY : Y.IsHermitian) :
    ∀ᶠ w : ℝ in 𝓝 0, ((1 : Matrix ι ι ℂ) - (w : ℂ) • Y).PosDef := by
  have he : ∀ᶠ w : ℝ in 𝓝 0, ∀ i, 0 < 1 - w * hY.eigenvalues i := by
    apply Filter.eventually_all.mpr
    intro i
    have hc : ContinuousAt (fun w : ℝ => 1 - w * hY.eigenvalues i) 0 := by fun_prop
    exact continuousAt_const.eventually_lt hc (by simp)
  exact he.mono fun w hw => one_sub_real_smul_posDef hY w hw

/-- Every exterior root is real whenever the real numerator is positive
definite. No diagonalizability of the product is asserted or required. -/
lemma exterior_root_im_eq_zero_of_posDef {H Y : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (hdet : IsUnit H.det) (w : ℝ)
    (hw : ((1 : Matrix ι ι ℂ) - (w : ℂ) • Y).PosDef)
    {a : ℂ} (ha : a ∈ (exteriorPencil H Y (w : ℂ)).charpoly.roots) : a.im = 0 := by
  have hs : a ∈ spectrum ℂ (exteriorPencil H Y (w : ℂ)) :=
    Matrix.mem_spectrum_of_isRoot_charpoly (Polynomial.isRoot_of_mem_roots ha)
  apply pencil_spectrum_im_eq_zero_of_definite hH hdet 0
    (Y := (1 : Matrix ι ι ℂ) - (w : ℂ) • Y)
  · exact Or.inl (by simpa using hw)
  · simpa [traceDensityPencil, exteriorPencil] using hs

/-- The actual normalized contour q is real for all sufficiently small real
w, exactly the reality fact used before the source Schwarz-slit argument. -/
theorem eventually_exteriorClusterQ_im_eq_zero {H Y : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (hY : Y.IsHermitian) (hdet : IsUnit H.det) :
    ∀ᶠ w : ℝ in 𝓝 0, (exteriorClusterQ H Y (w : ℂ)).im = 0 := by
  classical
  let R := negativeClusterRadius H⁻¹.charpoly.roots
  have hR : 0 ≤ R := (negativeClusterRadius_pos _).le
  have hcast : Tendsto (fun w : ℝ => (w : ℂ)) (𝓝 0) (𝓝 (0 : ℂ)) := by
    simpa using Complex.continuous_ofReal.tendsto (0 : ℝ)
  have hres := hcast.eventually (eventually_exterior_fixed_circle_resolvent Y hH hdet)
  filter_upwards [hres, eventually_one_sub_real_smul_posDef hY] with w hw hp
  have hsep : ∀ a ∈ (exteriorPencil H Y (w : ℂ)).charpoly.roots,
      a ∉ sphere (-(R : ℂ)) R := by
    intro a ha hs
    exact hw a hs
      (Matrix.mem_spectrum_of_isRoot_charpoly (Polynomial.isRoot_of_mem_roots ha))
  have hsum : (((exteriorPencil H Y (w : ℂ)).charpoly.roots.map
      (fun a => if a ∈ ball (-(R : ℂ)) R then a else 0)).sum).im = 0 := by
    apply multiset_sum_im_eq_zero
    intro a ha
    obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.mp ha
    split_ifs
    · exact exterior_root_im_eq_zero_of_posDef hH hdet w hp hb
    · simp
  change (circleClusterTrace (exteriorPencil H Y (w : ℂ)) (-(R : ℂ)) R).im = 0
  rw [circleClusterTrace_eq_root_sum _ hR hsep]
  rw [Complex.div_im, hsum]
  simp

/-- In particular the constant term of the actual analytic q is real. -/
theorem exteriorClusterQ_zero_im_eq_zero {H Y : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (hY : Y.IsHermitian) (hdet : IsUnit H.det) :
    (exteriorClusterQ H Y 0).im = 0 := by
  simpa using (eventually_exteriorClusterQ_im_eq_zero hH hY hdet).self_of_nhds

end
end CGLMPBounds.Hardy
