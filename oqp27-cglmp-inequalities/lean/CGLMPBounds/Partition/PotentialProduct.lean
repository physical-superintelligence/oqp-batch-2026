module

public import CGLMPBounds.Partition.PotentialCotangentCenter
public import CGLMPBounds.Partition.PotentialIdentity

@[expose] public section


/-! The literal D.8 identity (v f)'' = b−S on the open unit interval. -/

namespace CGLMPBounds.Partition
open Set Filter
open scoped Topology
noncomputable section

lemma potential_secant_product_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    partitionPotential x * scalarSecant x =
      -(1 : ℝ) / 2 * (x * (1 - x) * scalarSecant x - 2 * x / Real.pi) -
        1 / (2 * Real.pi) + regularizedCotangentMoment (x - 1 / 2) / Real.pi := by
  have hp := Real.pi_ne_zero
  have hsqrt : Real.sqrt 2 ≠ 0 := by positivity
  have hsqrt2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  by_cases hhalf : x = 1 / 2
  · subst x
    rw [partitionPotential_half]
    unfold scalarSecant regularizedCotangentMoment
    rw [show Real.pi * (1 / 2) / 2 = Real.pi / 4 by ring, Real.cos_pi_div_four]
    norm_num only [sub_self, mul_zero, Real.cos_zero, Real.sinc_zero, div_one]
    field_simp [hp, hsqrt]
    <;> ring_nf
    <;> simp only [hsqrt2]
    <;> ring
  let z : ℝ := (Real.pi / 2) * (x - 1 / 2)
  have hz : z ≠ 0 := mul_ne_zero (by positivity) (sub_ne_zero.mpr hhalf)
  have hza : |z| < Real.pi := by
    rw [abs_lt]
    dsimp [z]
    constructor <;> nlinarith [Real.pi_pos, hx.1, hx.2]
  have hsz : Real.sin z ≠ 0 := by
    have h := (Real.sinc_pos hza).ne'
    rw [Real.sinc_of_ne_zero hz] at h
    exact (div_ne_zero_iff.mp h).1
  have hsin : Real.sin (Real.pi * x / 2) ≠ 0 := by
    apply (Real.sin_pos_of_pos_of_lt_pi _ _).ne'
    · exact div_pos (mul_pos Real.pi_pos hx.1) (by norm_num)
    · nlinarith [Real.pi_pos, hx.2]
  have hcos : Real.cos (Real.pi * x / 2) ≠ 0 := by
    apply (Real.cos_pos_of_mem_Ioo _).ne'
    constructor <;> nlinarith [Real.pi_pos, hx.1, hx.2]
  have hangle : Real.pi * x / 2 = z + Real.pi / 4 := by dsimp [z]; ring
  have hs : Real.sin (Real.pi * x / 2) =
      (Real.sin z + Real.cos z) * Real.sqrt 2 / 2 := by
    rw [hangle, Real.sin_add, Real.sin_pi_div_four, Real.cos_pi_div_four]
    ring
  have hc : Real.cos (Real.pi * x / 2) =
      (Real.cos z - Real.sin z) * Real.sqrt 2 / 2 := by
    rw [hangle, Real.cos_add, Real.sin_pi_div_four, Real.cos_pi_div_four]
    ring
  have hden : 1 / Real.cos (Real.pi * x / 2) - 1 / Real.sin (Real.pi * x / 2) =
      (Real.sqrt 2 * Real.sin z) /
        (Real.sin (Real.pi * x / 2) * Real.cos (Real.pi * x / 2)) := by
    field_simp [hsin, hcos]
    rw [hs, hc]
    ring
  have hcorr : (2 * x - 1) /
      (Real.pi * (1 / Real.cos (Real.pi * x / 2) - 1 / Real.sin (Real.pi * x / 2))) *
        (1 / Real.cos (Real.pi * x / 2)) =
      (x - 1 / 2) / Real.pi + regularizedCotangentMoment (x - 1 / 2) / Real.pi := by
    rw [regularizedCotangentMoment_eq (sub_ne_zero.mpr hhalf), hden]
    change _ = (x - 1 / 2) / Real.pi +
      ((x - 1 / 2) * Real.cos z / Real.sin z) / Real.pi
    field_simp [hp, hsqrt, hsz, hsin, hcos]
    simp only [mul_comm x Real.pi]
    rw [mul_div_cancel_right₀ _ hcos, hs]
    ring
  simp only [partitionPotential, if_neg (not_or_intro hx.1.ne' hx.2.ne), if_neg hhalf,
    scalarSecant, add_mul]
  rw [hcorr]
  ring

/-- Exact source coefficient identity used to pass from D.7 to D.8. -/
theorem potential_secant_product_second {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    iteratedDeriv 2 (fun t => partitionPotential t * scalarSecant t) x =
      scalarCorrectionB x - scalarPartitionS x := by
  let A : ℝ → ℝ := fun t => t * (1 - t) * scalarSecant t - 2 * t / Real.pi
  let C : ℝ → ℝ := fun t => regularizedCotangentMoment (t - 1 / 2) / Real.pi
  have hcos : Real.cos (Real.pi * x / 2) ≠ 0 := by
    apply (Real.cos_pos_of_mem_Ioo _).ne'
    constructor <;> nlinarith [Real.pi_pos, hx.1, hx.2]
  have hA : ContDiffAt ℝ 2 A x := by
    dsimp [A, scalarSecant]
    fun_prop (disch := assumption)
  have hu : |x - 1 / 2| ≤ 1 / 2 := by
    rw [abs_le]
    constructor <;> linarith [hx.1, hx.2]
  have hC : ContDiffAt ℝ 2 C x := by
    apply AnalyticAt.contDiffAt
    exact ((analyticAt_regularizedCotangentMoment (hu.trans (by norm_num))).comp
      (f := fun t : ℝ => t - 1 / 2) (x := x)
      (by fun_prop : AnalyticAt ℝ (fun t : ℝ => t - 1 / 2) x)).div_const (c := Real.pi)
  have he : (fun t => partitionPotential t * scalarSecant t) =ᶠ[𝓝 x]
      (fun t => (-(1 : ℝ) / 2 * A t - 1 / (2 * Real.pi)) + C t) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with t ht
    exact potential_secant_product_eq ht
  have hscale : ContDiffAt ℝ 2 (fun t => -(1 : ℝ) / 2 * A t) x :=
    contDiffAt_const.mul hA
  have hsub : ContDiffAt ℝ 2 (fun t => -(1 : ℝ) / 2 * A t - 1 / (2 * Real.pi)) x :=
    hscale.sub contDiffAt_const
  rw [he.iteratedDeriv_eq 2,
    iteratedDeriv_fun_add hsub hC,
    iteratedDeriv_fun_sub hscale contDiffAt_const,
    iteratedDeriv_const_mul_field]
  have hconst : iteratedDeriv 2 (fun _ : ℝ => 1 / (2 * Real.pi)) x = 0 := by
    norm_num [iteratedDeriv_const]
  rw [hconst, sub_zero]
  have hcder : iteratedDeriv 2 C x = -scalarPartitionS x := by
    change iteratedDeriv 2
      (fun t => (fun u : ℝ => regularizedCotangentMoment u / Real.pi) (t - 1 / 2)) x = _
    rw [iteratedDeriv_comp_sub_const (f := fun u : ℝ => regularizedCotangentMoment u / Real.pi)
      (s := (1 / 2 : ℝ))]
    dsimp only
    rw [regularizedCotangentMoment_second hu]
    rfl
  rw [hcder]
  change -(1 : ℝ) / 2 * iteratedDeriv 2 A x - scalarPartitionS x = _
  rfl

end
end CGLMPBounds.Partition
