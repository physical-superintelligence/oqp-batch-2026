module

public import Mathlib

@[expose] public section


/-! A boundary form of uniqueness for actual analytic second derivatives.
The two boundary limits, including the first derivative, are explicit
premises and are discharged for the C.14 integral/series representations. -/

namespace CGLMPBounds.Hardy
noncomputable section
open Set Filter
open scoped Topology

theorem analytic_eqOn_of_second_derivative_boundary_limits
    {S : Set ℂ} (hS : IsOpen S) (hcS : IsPreconnected S)
    {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f S) (hg : AnalyticOnNhd ℂ g S)
    (hsecond : ∀ z ∈ S, iteratedDeriv 2 f z = iteratedDeriv 2 g z)
    {α : Type*} {l : Filter α} [NeBot l] (γ : α → ℂ)
    (hγ : ∀ᶠ a in l, γ a ∈ S) {c d : ℂ}
    (hfv : Tendsto (fun a => f (γ a)) l (𝓝 c))
    (hgv : Tendsto (fun a => g (γ a)) l (𝓝 c))
    (hfd : Tendsto (fun a => deriv f (γ a)) l (𝓝 d))
    (hgd : Tendsto (fun a => deriv g (γ a)) l (𝓝 d)) :
    EqOn f g S := by
  let F : ℂ → ℂ := fun z => f z - g z
  have hF : AnalyticOnNhd ℂ F S := hf.sub hg
  have hD : ∀ z ∈ S, deriv F z = deriv f z - deriv g z := by
    intro z hz
    exact ((hf z hz).differentiableAt.hasDerivAt.sub
      (hg z hz).differentiableAt.hasDerivAt).deriv
  have hDD : EqOn (deriv (deriv F)) 0 S := by
    intro z hz
    have he := iteratedDeriv_fun_sub (n := 2) (hf z hz).contDiffAt (hg z hz).contDiffAt
    rw [hsecond z hz, sub_self] at he
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero, Pi.zero_apply] using he
  obtain ⟨A, hA⟩ := hS.exists_is_const_of_deriv_eq_zero hcS
    (fun z hz => (hF z hz).deriv.differentiableAt.differentiableWithinAt) hDD
  have hDlim : Tendsto (fun a => deriv F (γ a)) l (𝓝 (0 : ℂ)) := by
    have hl := hfd.sub hgd
    rw [sub_self] at hl
    apply hl.congr'
    exact hγ.mono fun a ha => (hD _ ha).symm
  have hAlim : Tendsto (fun a => deriv F (γ a)) l (𝓝 A) :=
    tendsto_const_nhds.congr' (hγ.mono fun a ha => (hA _ ha).symm)
  have hA0 : A = 0 := tendsto_nhds_unique hAlim hDlim
  obtain ⟨B, hB⟩ := hS.exists_is_const_of_deriv_eq_zero hcS hF.differentiableOn
    (fun z hz => (hA z hz).trans hA0)
  have hFlim : Tendsto (fun a => F (γ a)) l (𝓝 (0 : ℂ)) := by
    simpa only [F, sub_self] using hfv.sub hgv
  have hBlim : Tendsto (fun a => F (γ a)) l (𝓝 B) :=
    tendsto_const_nhds.congr' (hγ.mono fun a ha => (hB _ ha).symm)
  have hB0 : B = 0 := tendsto_nhds_unique hBlim hFlim
  intro z hz
  exact sub_eq_zero.mp ((hB z hz).trans hB0)

end
end CGLMPBounds.Hardy
