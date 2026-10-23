module

public import CGLMPBounds.Hardy.UpperClusterAnalytic
public import CGLMPBounds.Hardy.DensityContinuity

@[expose] public section


/-!
# The imaginary boundary data of the source upper-cluster trace

For an arbitrary matrix, twice the imaginary part of the unnormalized upper
root sum is the sum of absolute imaginary parts plus the imaginary part of
the trace. The full characteristic-root multiset retains all multiplicities.
After division by the dimension this gives the exact factor `1 / (2*r)`.

The right side is continuous for all complex matrices, even when roots meet
the real axis. On a real Hermitian pencil the trace is real, so the imaginary
part of the source `g` has boundary value `pi * traceDensity`. This proves that
boundary datum without claiming continuity of the full selected complex root
sum. The auxiliary rotation `(-I/pi)*g` is holomorphic above the real axis and
has real boundary value equal to the literal density; it is not given a source
name or used as an assumed Schwarz-integral representation.

Canonical source: supplement Lemma C.3, printed page 8, with the convention
`L(z) = H⁻¹ * (Y - z I)`. C.8's Cauchy representation and moments remain open.
-/

open Complex Matrix Filter Set
open scoped Topology Matrix.Norms.Operator

namespace CGLMPBounds.Hardy
noncomputable section

/-- The elementary identity remains valid for real roots and counts repeated
roots with their full multiplicities. -/
lemma upper_root_sum_im (s : Multiset ℂ) :
    ((s.map (fun a => if 0 < a.im then a else 0)).sum).im =
      ((s.map (fun a => |a.im|)).sum + s.sum.im) / 2 := by
  classical
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Complex.add_im]
    by_cases ha : 0 < a.im
    · rw [if_pos ha, abs_of_pos ha]
      linarith
    · rw [if_neg ha, Complex.zero_im, abs_of_nonpos (le_of_not_gt ha)]
      linarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

/-- Exact normalization for the source's dimension-normalized root sum.
The totalized statement also holds in dimension zero. -/
theorem upperClusterTrace_im (A : Matrix ι ι ℂ) :
    (upperClusterTrace A).im =
      ((A.charpoly.roots.map (fun a => |a.im|)).sum + (Matrix.trace A).im) /
        (2 * (Fintype.card ι : ℝ)) := by
  rw [upperClusterTrace, Complex.div_natCast_im, upper_root_sum_im, div_div,
    ← Matrix.trace_eq_sum_roots_charpoly A]

/-- Only the imaginary part is claimed continuous. It is a symmetric sum of
continuous root observables, even though the selected complex root sum can jump
as a root crosses the real axis. -/
theorem continuous_upperClusterTrace_im :
    Continuous (fun A : Matrix ι ι ℂ => (upperClusterTrace A).im) := by
  have hs := continuous_charpoly_root_sum (ι := ι) (fun a : ℂ => |a.im|)
    (by fun_prop)
  have ht : Continuous (fun A : Matrix ι ι ℂ => (Matrix.trace A).im) :=
    Complex.continuous_im.comp continuous_id.matrix_trace
  exact ((hs.add ht).div_const (2 * (Fintype.card ι : ℝ))).congr
    (fun A => (upperClusterTrace_im A).symm)

/-- Cyclicity of trace suffices; the two Hermitian matrices need not commute. -/
lemma trace_mul_hermitian_im {A B : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (Matrix.trace (A * B)).im = 0 := by
  have hs : star (Matrix.trace (A * B)) = Matrix.trace (A * B) := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hA.eq, hB.eq,
      Matrix.trace_mul_comm]
  have hi := congrArg Complex.im hs
  simp only [Complex.star_def, Complex.conj_im] at hi
  linarith

/-- The trace of the literal real pencil is real. This algebraic fact does not
need invertibility, since the totalized matrix inverse preserves Hermiticity. -/
lemma trace_traceDensityPencil_real_im {H Y : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (hY : Y.IsHermitian) (y : ℝ) :
    (Matrix.trace (traceDensityPencil H Y (y : ℂ))).im = 0 := by
  have hy : IsSelfAdjoint (y : ℂ) := by simp [IsSelfAdjoint, Complex.star_def]
  exact trace_mul_hermitian_im hH.inv (hY.sub (Matrix.isHermitian_one.smul hy))

/-- The same reality fact for the opposite sign convention, stated explicitly
rather than silently changing the source pencil. -/
lemma trace_opposite_real_pencil_im {H Y : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (hY : Y.IsHermitian) (y : ℝ) :
    (Matrix.trace (H⁻¹ * ((y : ℂ) • (1 : Matrix ι ι ℂ) - Y))).im = 0 := by
  have hy : IsSelfAdjoint (y : ℂ) := by simp [IsSelfAdjoint, Complex.star_def]
  exact trace_mul_hermitian_im hH.inv ((Matrix.isHermitian_one.smul hy).sub hY)

/-- The exact pointwise boundary value asserted in the proof of C.3, with the
source's `Y-yI` sign and the literal density normalization. -/
theorem pencil_upperClusterTrace_im_real {H Y : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (hY : Y.IsHermitian) (y : ℝ) :
    (upperClusterTrace (traceDensityPencil H Y (y : ℂ))).im =
      Real.pi * traceDensity H Y y := by
  rw [upperClusterTrace_im, trace_traceDensityPencil_real_im hH hY y, add_zero]
  unfold traceDensity
  conv_rhs =>
    rw [show 2 * Real.pi * (Fintype.card ι : ℝ) =
      (2 * (Fintype.card ι : ℝ)) * Real.pi by ring, ← div_div]
  exact (mul_div_cancel₀ _ Real.pi_ne_zero).symm

/-- Continuity on the entire complex parameter plane of the imaginary part of
the source root sum. It does not assert global continuity of `g` itself. -/
theorem continuous_pencil_upperClusterTrace_im (H Y : Matrix ι ι ℂ) :
    Continuous (fun z : ℂ => (upperClusterTrace (traceDensityPencil H Y z)).im) := by
  have hp : Continuous (traceDensityPencil H Y) := by
    unfold traceDensityPencil
    fun_prop
  exact continuous_upperClusterTrace_im.comp hp

/-- The boundary limit is valid along every approach from the upper half-plane,
including at repeated real roots and endpoints of the spectral interval. -/
theorem tendsto_pencil_upperClusterTrace_im_boundary {H Y : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (hY : Y.IsHermitian) (y : ℝ) :
    Tendsto (fun z : ℂ => (upperClusterTrace (traceDensityPencil H Y z)).im)
      (𝓝[{z : ℂ | 0 < z.im}] (y : ℂ)) (𝓝 (Real.pi * traceDensity H Y y)) := by
  have ht := (continuous_pencil_upperClusterTrace_im H Y).tendsto (y : ℂ)
  rw [pencil_upperClusterTrace_im_real hH hY y] at ht
  exact ht.mono_left nhdsWithin_le_nhds

/-- Multiplication by `-I/pi` converts the imaginary boundary datum into a real
boundary datum. This is an auxiliary rotation, not a new source definition. -/
lemma rotated_complex_re (v : ℂ) :
    ((-Complex.I / (Real.pi : ℂ)) * v).re = v.im / Real.pi := by
  simp only [Complex.mul_re, Complex.div_ofReal_re, Complex.div_ofReal_im,
    Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im]
  ring

theorem continuous_rotated_pencil_upperClusterTrace_re (H Y : Matrix ι ι ℂ) :
    Continuous (fun z : ℂ =>
      ((-Complex.I / (Real.pi : ℂ)) * upperClusterTrace (traceDensityPencil H Y z)).re) := by
  simp_rw [rotated_complex_re]
  exact (continuous_pencil_upperClusterTrace_im H Y).div_const Real.pi

theorem rotated_pencil_upperClusterTrace_re_real {H Y : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (hY : Y.IsHermitian) (y : ℝ) :
    ((-Complex.I / (Real.pi : ℂ)) *
      upperClusterTrace (traceDensityPencil H Y (y : ℂ))).re = traceDensity H Y y := by
  rw [rotated_complex_re, pencil_upperClusterTrace_im_real hH hY y,
    mul_div_cancel_left₀ _ Real.pi_ne_zero]

theorem tendsto_rotated_pencil_upperClusterTrace_re_boundary {H Y : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (hY : Y.IsHermitian) (y : ℝ) :
    Tendsto (fun z : ℂ =>
      ((-Complex.I / (Real.pi : ℂ)) * upperClusterTrace (traceDensityPencil H Y z)).re)
      (𝓝[{z : ℂ | 0 < z.im}] (y : ℂ)) (𝓝 (traceDensity H Y y)) := by
  have ht := (continuous_rotated_pencil_upperClusterTrace_re H Y).tendsto (y : ℂ)
  rw [rotated_pencil_upperClusterTrace_re_real hH hY y] at ht
  exact ht.mono_left nhdsWithin_le_nhds

/-- Holomorphy of the same auxiliary rotation, now using precisely the source
invertibility hypothesis needed for the upper-cluster analytic theorem. -/
theorem analyticOnNhd_rotated_pencil_upperClusterTrace {H Y : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (hY : Y.IsHermitian) (hdet : IsUnit H.det) :
    AnalyticOnNhd ℂ (fun z =>
      (-Complex.I / (Real.pi : ℂ)) * upperClusterTrace (traceDensityPencil H Y z))
      {z : ℂ | 0 < z.im} := by
  intro z hz
  exact analyticAt_const.mul (analyticOnNhd_pencil_upperClusterTrace hH hY hdet z hz)

end
end CGLMPBounds.Hardy
