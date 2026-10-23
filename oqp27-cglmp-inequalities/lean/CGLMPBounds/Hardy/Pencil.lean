module

public import CGLMPBounds.Defs.TraceDensity

@[expose] public section


/-!
# Elementary pencil facts in Lemma C.3

Reuse: Mathlib's Hermitian quadratic-form identity, eigenvector/spectrum
equivalence, and characteristic polynomial roots. No diagonalizability of the
pencil is assumed. Holomorphic root clusters and the moment identity remain open.
-/

namespace CGLMPBounds.Hardy

open Matrix
open scoped ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem traceDensity_nonneg (H Y : Matrix ι ι ℂ) (y : ℝ) :
    0 ≤ traceDensity H Y y := by
  apply div_nonneg
  · apply Multiset.sum_nonneg
    intro t ht
    obtain ⟨z, _, rfl⟩ := Multiset.mem_map.mp ht
    exact abs_nonneg _
  · positivity

theorem hermitian_quadratic_im {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (v : ι → ℂ) :
    (star v ⬝ᵥ (A *ᵥ v)).im = 0 := by
  have h := congrArg Complex.im (hA.star_dotProduct_mulVec_comm v v)
  simp only [Complex.star_def, Complex.conj_im] at h
  linarith

/-- The elementary identity displayed at the start of the proof of C.3. -/
theorem pencil_eigenvector_im_identity {H Y : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (hY : Y.IsHermitian) {z lam : ℂ} (v : ι → ℂ)
    (hv : (Y - z • (1 : Matrix ι ι ℂ)) *ᵥ v = lam • (H *ᵥ v)) :
    -z.im * (star v ⬝ᵥ v).re = lam.im * (star v ⬝ᵥ (H *ᵥ v)).re := by
  have h := congrArg (fun w : ι → ℂ => star v ⬝ᵥ w) hv
  have hHi := hermitian_quadratic_im hH v
  have hYi := hermitian_quadratic_im hY v
  have hVi : (star v ⬝ᵥ v).im = 0 := by
    have hh := hermitian_quadratic_im (Matrix.isHermitian_one :
      (1 : Matrix ι ι ℂ).IsHermitian) v
    simpa only [Matrix.one_mulVec] using hh
  simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul, smul_eq_mul] at h
  have hi := congrArg Complex.im h
  simp only [Complex.sub_im, Complex.mul_im, hHi, hYi, hVi, mul_zero, zero_add] at hi
  linarith

/-- A nonzero generalized eigenvector excludes a real eigenvalue above the real axis. -/
theorem generalized_pencil_eigenvalue_im_ne_zero {H Y : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (hY : Y.IsHermitian) {z lam : ℂ} (hz : 0 < z.im)
    {v : ι → ℂ} (hv0 : v ≠ 0)
    (hv : (Y - z • (1 : Matrix ι ι ℂ)) *ᵥ v = lam • (H *ᵥ v)) : lam.im ≠ 0 := by
  have hid := pencil_eigenvector_im_identity hH hY v hv
  have hpos : 0 < (star v ⬝ᵥ v).re :=
    (Complex.pos_iff.mp (Matrix.dotProduct_star_self_pos_iff.mpr hv0)).1
  intro hlam
  rw [hlam, zero_mul] at hid
  nlinarith [mul_pos hz hpos]

theorem pencil_generalized_eigenvector {H Y : Matrix ι ι ℂ} (hdet : IsUnit H.det)
    {z lam : ℂ} (hlam : lam ∈ spectrum ℂ (traceDensityPencil H Y z)) :
    ∃ v : ι → ℂ, v ≠ 0 ∧
      (Y - z • (1 : Matrix ι ι ℂ)) *ᵥ v = lam • (H *ᵥ v) := by
  have hlin : Module.End.HasEigenvalue (traceDensityPencil H Y z).toLin' lam := by
    apply Module.End.hasEigenvalue_iff_mem_spectrum.2
    simpa only [Matrix.spectrum_toLin'] using hlam
  obtain ⟨v, hv⟩ := hlin.exists_hasEigenvector
  have he := hv.apply_eq_smul
  rw [Matrix.toLin'_apply] at he
  have hm := congrArg (fun w : ι → ℂ => H *ᵥ w) he
  have hv' : (Y - z • (1 : Matrix ι ι ℂ)) *ᵥ v = lam • (H *ᵥ v) := by
    simpa only [traceDensityPencil, Matrix.mulVec_mulVec, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv H hdet, Matrix.one_mul, Matrix.mulVec_smul] using hm
  exact ⟨v, hv.2, hv'⟩

/-- The actual invertible pencil has no real eigenvalues in the upper half-plane. -/
theorem pencil_spectrum_im_ne_zero {H Y : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (hY : Y.IsHermitian) (hdet : IsUnit H.det)
    {z lam : ℂ} (hz : 0 < z.im) (hlam : lam ∈ spectrum ℂ (traceDensityPencil H Y z)) :
    lam.im ≠ 0 := by
  obtain ⟨v, hv0, hv⟩ := pencil_generalized_eigenvector hdet hlam
  exact generalized_pencil_eigenvalue_im_ne_zero hH hY hz hv0 hv

/-- Definite Hermitian numerator forces every pencil eigenvalue to be real.
The proof uses quadratic forms and does not assume diagonalizability. -/
theorem pencil_spectrum_im_eq_zero_of_definite {H Y : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (hdet : IsUnit H.det) (y : ℝ)
    (hC : (Y - (y : ℂ) • (1 : Matrix ι ι ℂ)).PosDef ∨
      (-(Y - (y : ℂ) • (1 : Matrix ι ι ℂ))).PosDef)
    {lam : ℂ} (hlam : lam ∈ spectrum ℂ (traceDensityPencil H Y (y : ℂ))) : lam.im = 0 := by
  obtain ⟨v, hv0, hv⟩ := pencil_generalized_eigenvector hdet hlam
  let C := Y - (y : ℂ) • (1 : Matrix ι ι ℂ)
  have hCre : (star v ⬝ᵥ (C *ᵥ v)).re ≠ 0 := by
    rcases hC with hp | hn
    · exact ne_of_gt (Complex.pos_iff.mp (hp.dotProduct_mulVec_pos hv0)).1
    · have h := (Complex.pos_iff.mp (hn.dotProduct_mulVec_pos hv0)).1
      simp only [Matrix.neg_mulVec, dotProduct_neg, Complex.neg_re] at h
      change -(star v ⬝ᵥ (C *ᵥ v)).re > 0 at h
      linarith
  have hCim : (star v ⬝ᵥ (C *ᵥ v)).im = 0 := by
    rcases hC with hp | hn
    · exact hermitian_quadratic_im hp.isHermitian v
    · have h := hermitian_quadratic_im hn.isHermitian v
      simp only [Matrix.neg_mulVec, dotProduct_neg, Complex.neg_im] at h
      change -(star v ⬝ᵥ (C *ᵥ v)).im = 0 at h
      linarith
  have hHim := hermitian_quadratic_im hH v
  have h := congrArg (fun w : ι → ℂ => star v ⬝ᵥ w) hv
  change star v ⬝ᵥ (C *ᵥ v) = star v ⬝ᵥ (lam • (H *ᵥ v)) at h
  rw [dotProduct_smul, smul_eq_mul] at h
  have hr := congrArg Complex.re h
  have hi := congrArg Complex.im h
  simp only [Complex.mul_re, hHim, mul_zero, sub_zero] at hr
  simp only [Complex.mul_im, hHim, hCim, mul_zero, zero_add] at hi
  have hHre : (star v ⬝ᵥ (H *ᵥ v)).re ≠ 0 := by
    intro hz
    apply hCre
    simpa only [hz, mul_zero] using hr
  exact (mul_eq_zero.mp hi.symm).resolve_right hHre

/-- The density vanishes wherever Y-yI is definite. Converting this to the
spectral interval of Y is a separate endpoint-support argument. -/
theorem traceDensity_eq_zero_of_definite {H Y : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (hdet : IsUnit H.det) (y : ℝ)
    (hC : (Y - (y : ℂ) • (1 : Matrix ι ι ℂ)).PosDef ∨
      (-(Y - (y : ℂ) • (1 : Matrix ι ι ℂ))).PosDef) : traceDensity H Y y = 0 := by
  unfold traceDensity
  have hz : (((traceDensityPencil H Y (y : ℂ)).charpoly.roots).map
      (fun z : ℂ => |z.im|)).sum = 0 := by
    apply Multiset.sum_eq_zero
    intro a ha
    obtain ⟨lam, hlam, rfl⟩ := Multiset.mem_map.mp ha
    have hs : lam ∈ spectrum ℂ (traceDensityPencil H Y (y : ℂ)) :=
      Matrix.mem_spectrum_of_isRoot_charpoly (Polynomial.isRoot_of_mem_roots hlam)
    rw [pencil_spectrum_im_eq_zero_of_definite hH hdet y hC hs, abs_zero]
  rw [hz, zero_div]

end CGLMPBounds.Hardy
