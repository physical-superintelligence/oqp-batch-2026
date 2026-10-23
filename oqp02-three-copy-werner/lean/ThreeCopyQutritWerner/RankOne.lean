module

public import ThreeCopyQutritWerner.Interior

@[expose] public section


/-!
# Nonzero endpoint zeros have rank two

Manuscript Section 5.1: every nonzero endpoint zero has rank two.  For a rank-one matrix
`C = x y†` let `w = x ⊗ y` on two replicas and let `Fᵢ` swap the `i`-th site of the two
replicas.  Then `‖Tr_S C‖_F² = ⟨w, F_S w⟩` for every set `S` of sites, so
`q(C) = ⟨w, ∏ᵢ (1 - Fᵢ/2) w⟩`, and `∏ᵢ (1 - Fᵢ/2) = (1/8) ∑_S ∏_{i ∈ S} (1 - Fᵢ)` gives

`8 q(C) = ∑_S ⟨w, ∏_{i ∈ S} (1 - Fᵢ) w⟩ ≥ ⟨w, w⟩ = ‖x‖² ‖y‖²`,

because each summand equals `2^{-|S|} ‖∏_{i ∈ S} (1 - Fᵢ) w‖² ≥ 0` (the `Fᵢ` are commuting
involutions).  Hence `q(C) ≥ N/8` on rank one (`endpointEnergy_ketBra_ge`), an endpoint
zero of rank at most one vanishes, and a nonzero endpoint zero of rank at most two has
rank exactly two.
-/

noncomputable section

open scoped ComplexConjugate

namespace ThreeCopyQutritWerner

section SwapAbstract

variable {I : Type*}

/-- `(1 - σ) f`, i.e. `p ↦ f p - f (σ p)`. -/
def swapAnti (σ : I ≃ I) (f : I → ℂ) (p : I) : ℂ := f p - f (σ p)

theorem swapAnti_self (σ : I ≃ I) (hσ : ∀ p, σ (σ p) = p) (f : I → ℂ) (p : I) :
    swapAnti σ f (σ p) = -swapAnti σ f p := by
  unfold swapAnti
  rw [hσ p]
  ring

theorem swapAnti_of_comm (σ τ : I ≃ I) (hc : ∀ p, σ (τ p) = τ (σ p)) (h : I → ℂ)
    (hh : ∀ p, h (τ p) = -h p) (p : I) :
    swapAnti σ h (τ p) = -swapAnti σ h p := by
  unfold swapAnti
  rw [hc p, hh p, hh (σ p)]
  ring

variable [Fintype I]

theorem sum_conj_mul_comp_of_swap (σ : I ≃ I) (hσ : ∀ p, σ (σ p) = p) (g F : I → ℂ)
    (hg : ∀ p, g (σ p) = -g p) :
    ∑ p, conj (g p) * F (σ p) = -∑ p, conj (g p) * F p := by
  calc ∑ p, conj (g p) * F (σ p)
      = ∑ p, conj (g (σ p)) * F (σ (σ p)) :=
        (Fintype.sum_equiv σ (fun p => conj (g (σ p)) * F (σ (σ p)))
          (fun q => conj (g q) * F (σ q)) (fun _ => rfl)).symm
    _ = ∑ p, -(conj (g p) * F p) :=
        Finset.sum_congr rfl fun p _ => by rw [hg p, hσ p, map_neg, neg_mul]
    _ = -∑ p, conj (g p) * F p := Finset.sum_neg_distrib _

theorem sum_conj_mul_swapAnti (σ : I ≃ I) (hσ : ∀ p, σ (σ p) = p) (g h : I → ℂ)
    (hg : ∀ p, g (σ p) = -g p) :
    ∑ p, conj (g p) * swapAnti σ h p = 2 * ∑ p, conj (g p) * h p := by
  have h1 := sum_conj_mul_comp_of_swap σ hσ g h hg
  have e : ∑ p, conj (g p) * swapAnti σ h p =
      ∑ p, (conj (g p) * h p - conj (g p) * h (σ p)) :=
    Finset.sum_congr rfl fun p _ => by unfold swapAnti; ring
  rw [e, Finset.sum_sub_distrib, h1]
  ring

/-- One involution: `∑ conj(g) g = 2 ∑ conj(g) f` for `g = (1 - σ) f`. -/
theorem sum_conj_swapAnti1_self (σ : I ≃ I) (hσ : ∀ p, σ (σ p) = p) (f : I → ℂ) :
    ∑ p, conj (swapAnti σ f p) * swapAnti σ f p = 2 * ∑ p, conj (swapAnti σ f p) * f p :=
  sum_conj_mul_swapAnti σ hσ (swapAnti σ f) f (swapAnti_self σ hσ f)

/-- Two commuting involutions: `∑ conj(g) g = 4 ∑ conj(g) f` for `g = (1 - σ)(1 - τ) f`. -/
theorem sum_conj_swapAnti2_self (σ τ : I ≃ I) (hσ : ∀ p, σ (σ p) = p) (hτ : ∀ p, τ (τ p) = p)
    (hc : ∀ p, σ (τ p) = τ (σ p)) (f : I → ℂ) :
    ∑ p, conj (swapAnti σ (swapAnti τ f) p) * swapAnti σ (swapAnti τ f) p =
      4 * ∑ p, conj (swapAnti σ (swapAnti τ f) p) * f p := by
  have gσ : ∀ p, swapAnti σ (swapAnti τ f) (σ p) = -swapAnti σ (swapAnti τ f) p :=
    swapAnti_self σ hσ (swapAnti τ f)
  have gτ : ∀ p, swapAnti σ (swapAnti τ f) (τ p) = -swapAnti σ (swapAnti τ f) p :=
    swapAnti_of_comm σ τ hc (swapAnti τ f) (swapAnti_self τ hτ f)
  rw [sum_conj_mul_swapAnti σ hσ (swapAnti σ (swapAnti τ f)) (swapAnti τ f) gσ,
    sum_conj_mul_swapAnti τ hτ (swapAnti σ (swapAnti τ f)) f gτ]
  ring

/-- Three commuting involutions: `∑ conj(g) g = 8 ∑ conj(g) f` for
`g = (1 - σ)(1 - τ)(1 - ρ) f`. -/
theorem sum_conj_swapAnti3_self (σ τ ρ : I ≃ I) (hσ : ∀ p, σ (σ p) = p)
    (hτ : ∀ p, τ (τ p) = p) (hρ : ∀ p, ρ (ρ p) = p) (hστ : ∀ p, σ (τ p) = τ (σ p))
    (hσρ : ∀ p, σ (ρ p) = ρ (σ p)) (hτρ : ∀ p, τ (ρ p) = ρ (τ p)) (f : I → ℂ) :
    ∑ p, conj (swapAnti σ (swapAnti τ (swapAnti ρ f)) p) *
        swapAnti σ (swapAnti τ (swapAnti ρ f)) p =
      8 * ∑ p, conj (swapAnti σ (swapAnti τ (swapAnti ρ f)) p) * f p := by
  have gσ : ∀ p, swapAnti σ (swapAnti τ (swapAnti ρ f)) (σ p) =
      -swapAnti σ (swapAnti τ (swapAnti ρ f)) p :=
    swapAnti_self σ hσ (swapAnti τ (swapAnti ρ f))
  have gτ : ∀ p, swapAnti σ (swapAnti τ (swapAnti ρ f)) (τ p) =
      -swapAnti σ (swapAnti τ (swapAnti ρ f)) p :=
    swapAnti_of_comm σ τ hστ (swapAnti τ (swapAnti ρ f)) (swapAnti_self τ hτ (swapAnti ρ f))
  have gρ : ∀ p, swapAnti σ (swapAnti τ (swapAnti ρ f)) (ρ p) =
      -swapAnti σ (swapAnti τ (swapAnti ρ f)) p :=
    swapAnti_of_comm σ ρ hσρ (swapAnti τ (swapAnti ρ f))
      (swapAnti_of_comm τ ρ hτρ (swapAnti ρ f) (swapAnti_self ρ hρ f))
  rw [sum_conj_mul_swapAnti σ hσ (swapAnti σ (swapAnti τ (swapAnti ρ f)))
      (swapAnti τ (swapAnti ρ f)) gσ,
    sum_conj_mul_swapAnti τ hτ (swapAnti σ (swapAnti τ (swapAnti ρ f))) (swapAnti ρ f) gτ,
    sum_conj_mul_swapAnti ρ hρ (swapAnti σ (swapAnti τ (swapAnti ρ f))) f gρ]
  ring

theorem sum_conj_swapAnti1_mul (σ : I ≃ I) (f : I → ℂ) :
    ∑ p, conj (swapAnti σ f p) * f p =
      ∑ p, conj (f p) * f p - ∑ p, conj (f (σ p)) * f p := by
  calc ∑ p, conj (swapAnti σ f p) * f p
      = ∑ p, (conj (f p) * f p - conj (f (σ p)) * f p) :=
        Finset.sum_congr rfl fun p _ => by simp only [swapAnti, map_sub]; ring
    _ = _ := by simp only [Finset.sum_sub_distrib]

theorem sum_conj_swapAnti2_mul (σ τ : I ≃ I) (f : I → ℂ) :
    ∑ p, conj (swapAnti σ (swapAnti τ f) p) * f p =
      ∑ p, conj (f p) * f p - ∑ p, conj (f (τ p)) * f p - ∑ p, conj (f (σ p)) * f p
        + ∑ p, conj (f (τ (σ p))) * f p := by
  calc ∑ p, conj (swapAnti σ (swapAnti τ f) p) * f p
      = ∑ p, (conj (f p) * f p - conj (f (τ p)) * f p - conj (f (σ p)) * f p
          + conj (f (τ (σ p))) * f p) :=
        Finset.sum_congr rfl fun p _ => by simp only [swapAnti, map_sub]; ring
    _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]

theorem sum_conj_swapAnti3_mul (σ τ ρ : I ≃ I) (f : I → ℂ) :
    ∑ p, conj (swapAnti σ (swapAnti τ (swapAnti ρ f)) p) * f p =
      ∑ p, conj (f p) * f p - ∑ p, conj (f (ρ p)) * f p - ∑ p, conj (f (τ p)) * f p
        + ∑ p, conj (f (ρ (τ p))) * f p - ∑ p, conj (f (σ p)) * f p
        + ∑ p, conj (f (ρ (σ p))) * f p + ∑ p, conj (f (τ (σ p))) * f p
        - ∑ p, conj (f (ρ (τ (σ p)))) * f p := by
  calc ∑ p, conj (swapAnti σ (swapAnti τ (swapAnti ρ f)) p) * f p
      = ∑ p, (conj (f p) * f p - conj (f (ρ p)) * f p - conj (f (τ p)) * f p
          + conj (f (ρ (τ p))) * f p - conj (f (σ p)) * f p
          + conj (f (ρ (σ p))) * f p + conj (f (τ (σ p))) * f p
          - conj (f (ρ (τ (σ p)))) * f p) :=
        Finset.sum_congr rfl fun p _ => by simp only [swapAnti, map_sub]; ring
    _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]

/-- If `∑ conj(g) g = k ∑ conj(g) f` with `k > 0` and `∑ conj(g) f = r` is real, then
`r ≥ 0`. -/
theorem nonneg_of_sum_conj_eq (g f : I → ℂ) (k r : ℝ) (hk : 0 < k)
    (h1 : ∑ p, conj (g p) * g p = (k : ℂ) * ∑ p, conj (g p) * f p)
    (h2 : ∑ p, conj (g p) * f p = (r : ℂ)) : 0 ≤ r := by
  have hn : ∑ p, conj (g p) * g p = ((∑ p, Complex.normSq (g p) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun p _ => Complex.normSq_eq_conj_mul_self.symm
  have h3 : ((∑ p, Complex.normSq (g p) : ℝ) : ℂ) = ((k * r : ℝ) : ℂ) := by
    rw [← hn, h1, h2, Complex.ofReal_mul]
  have h4 : ∑ p, Complex.normSq (g p) = k * r := Complex.ofReal_injective h3
  have h5 : 0 ≤ ∑ p, Complex.normSq (g p) :=
    Finset.sum_nonneg fun p _ => Complex.normSq_nonneg _
  rw [h4] at h5
  by_contra hr
  have h7 : k * r < 0 := mul_neg_of_pos_of_neg hk (not_le.mp hr)
  linarith

end SwapAbstract

/-- The product vector `x ⊗ y` on two replicas. -/
def tensorVec {ι : Type*} (x y : ι → ℂ) (p : ι × ι) : ℂ := x p.1 * y p.2

section SiteSwaps

variable {a b c : Type*}

/-- Exchange the site-1 components of two replicas (`F₁`). -/
def siteSwap₁ : (a × b × c) × (a × b × c) ≃ (a × b × c) × (a × b × c) where
  toFun p := ((p.2.1, p.1.2), (p.1.1, p.2.2))
  invFun p := ((p.2.1, p.1.2), (p.1.1, p.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- Exchange the site-2 components of two replicas (`F₂`). -/
def siteSwap₂ : (a × b × c) × (a × b × c) ≃ (a × b × c) × (a × b × c) where
  toFun p := ((p.1.1, p.2.2.1, p.1.2.2), (p.2.1, p.1.2.1, p.2.2.2))
  invFun p := ((p.1.1, p.2.2.1, p.1.2.2), (p.2.1, p.1.2.1, p.2.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- Exchange the site-3 components of two replicas (`F₃`). -/
def siteSwap₃ : (a × b × c) × (a × b × c) ≃ (a × b × c) × (a × b × c) where
  toFun p := ((p.1.1, p.1.2.1, p.2.2.2), (p.2.1, p.2.2.1, p.1.2.2))
  invFun p := ((p.1.1, p.1.2.1, p.2.2.2), (p.2.1, p.2.2.1, p.1.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

theorem siteSwap₁_invol (p : (a × b × c) × (a × b × c)) : siteSwap₁ (siteSwap₁ p) = p := rfl

theorem siteSwap₂_invol (p : (a × b × c) × (a × b × c)) : siteSwap₂ (siteSwap₂ p) = p := rfl

theorem siteSwap₃_invol (p : (a × b × c) × (a × b × c)) : siteSwap₃ (siteSwap₃ p) = p := rfl

theorem siteSwap₁₂_comm (p : (a × b × c) × (a × b × c)) :
    siteSwap₁ (siteSwap₂ p) = siteSwap₂ (siteSwap₁ p) := rfl

theorem siteSwap₁₃_comm (p : (a × b × c) × (a × b × c)) :
    siteSwap₁ (siteSwap₃ p) = siteSwap₃ (siteSwap₁ p) := rfl

theorem siteSwap₂₃_comm (p : (a × b × c) × (a × b × c)) :
    siteSwap₂ (siteSwap₃ p) = siteSwap₃ (siteSwap₂ p) := rfl

variable [Fintype a] [Fintype b] [Fintype c]

/-! ### The swap identities `‖Tr_S (x y†)‖_F² = ⟨F_S w, w⟩` -/

theorem sum_tensorVec_self (x y : a × b × c → ℂ) :
    ∑ p, conj (tensorVec x y p) * tensorVec x y p = ((vecNormSq x * vecNormSq y : ℝ) : ℂ) :=
  sum_conj_tensor_self x y

theorem sum_tensorVec_swap₁ (x y : a × b × c → ℂ) :
    ∑ p, conj (tensorVec x y (siteSwap₁ p)) * tensorVec x y p =
      ((frobSq (ptrace₁ (ketBra x y)) : ℝ) : ℂ) :=
  sum_conj_tensor_swapLeft x y

theorem ptrace₂₃_ketBra_eq_ptraceR (x y : a × b × c → ℂ) :
    ptrace₂₃ (ketBra x y) = ptraceR (ketBra x y) := by
  ext i i'
  simp only [ptrace₂₃, ptraceR, Fintype.sum_prod_type]
  first | done | rfl

theorem sum_tensorVec_swap₂₃ (x y : a × b × c → ℂ) :
    ∑ p, conj (tensorVec x y (siteSwap₃ (siteSwap₂ p))) * tensorVec x y p =
      ((frobSq (ptrace₂₃ (ketBra x y)) : ℝ) : ℂ) := by
  rw [ptrace₂₃_ketBra_eq_ptraceR]
  exact sum_conj_tensor_swapRight x y

theorem sum_tensorVec_swap₁₂₃ (x y : a × b × c → ℂ) :
    ∑ p, conj (tensorVec x y (siteSwap₃ (siteSwap₂ (siteSwap₁ p)))) * tensorVec x y p =
      ((Complex.normSq (ketBra x y).trace : ℝ) : ℂ) := by
  rw [trace_ketBra]
  exact sum_conj_tensor_swap x y

theorem sum_tensorVec_swap₂ (x y : a × b × c → ℂ) :
    ∑ p, conj (tensorVec x y (siteSwap₂ p)) * tensorVec x y p =
      ((frobSq (ptrace₂ (ketBra x y)) : ℝ) : ℂ) :=
  (Fintype.sum_equiv
    (Equiv.prodCongr (siteEquiv₂ : b × a × c ≃ a × b × c) (siteEquiv₂ : b × a × c ≃ a × b × c))
    (fun q : (b × a × c) × (b × a × c) =>
      conj (x (q.1.2.1, q.2.1, q.1.2.2) * y (q.2.2.1, q.1.1, q.2.2.2)) *
        (x (q.1.2.1, q.1.1, q.1.2.2) * y (q.2.2.1, q.2.1, q.2.2.2)))
    (fun p => conj (tensorVec x y (siteSwap₂ p)) * tensorVec x y p)
    (fun _ => rfl)).symm.trans
    (sum_conj_tensor_swapLeft (fun s : b × a × c => x (s.2.1, s.1, s.2.2))
      (fun s : b × a × c => y (s.2.1, s.1, s.2.2)))

theorem ptraceR_ketBra_regroup₂ (x y : a × b × c → ℂ) :
    ptraceR (ketBra (fun s : b × a × c => x (s.2.1, s.1, s.2.2))
      (fun s : b × a × c => y (s.2.1, s.1, s.2.2))) = ptrace₁₃ (ketBra x y) := by
  ext j j'
  simp only [ptrace₁₃, ptraceR, Fintype.sum_prod_type]
  first | done | rfl

theorem sum_tensorVec_swap₁₃ (x y : a × b × c → ℂ) :
    ∑ p, conj (tensorVec x y (siteSwap₃ (siteSwap₁ p))) * tensorVec x y p =
      ((frobSq (ptrace₁₃ (ketBra x y)) : ℝ) : ℂ) := by
  rw [← ptraceR_ketBra_regroup₂]
  exact (Fintype.sum_equiv
    (Equiv.prodCongr (siteEquiv₂ : b × a × c ≃ a × b × c) (siteEquiv₂ : b × a × c ≃ a × b × c))
    (fun q : (b × a × c) × (b × a × c) =>
      conj (x (q.2.2.1, q.1.1, q.2.2.2) * y (q.1.2.1, q.2.1, q.1.2.2)) *
        (x (q.1.2.1, q.1.1, q.1.2.2) * y (q.2.2.1, q.2.1, q.2.2.2)))
    (fun p => conj (tensorVec x y (siteSwap₃ (siteSwap₁ p))) * tensorVec x y p)
    (fun _ => rfl)).symm.trans
    (sum_conj_tensor_swapRight (fun s : b × a × c => x (s.2.1, s.1, s.2.2))
      (fun s : b × a × c => y (s.2.1, s.1, s.2.2)))

theorem sum_tensorVec_swap₃ (x y : a × b × c → ℂ) :
    ∑ p, conj (tensorVec x y (siteSwap₃ p)) * tensorVec x y p =
      ((frobSq (ptrace₃ (ketBra x y)) : ℝ) : ℂ) :=
  (Fintype.sum_equiv
    (Equiv.prodCongr (siteEquiv₃ : c × a × b ≃ a × b × c) (siteEquiv₃ : c × a × b ≃ a × b × c))
    (fun q : (c × a × b) × (c × a × b) =>
      conj (x (q.1.2.1, q.1.2.2, q.2.1) * y (q.2.2.1, q.2.2.2, q.1.1)) *
        (x (q.1.2.1, q.1.2.2, q.1.1) * y (q.2.2.1, q.2.2.2, q.2.1)))
    (fun p => conj (tensorVec x y (siteSwap₃ p)) * tensorVec x y p)
    (fun _ => rfl)).symm.trans
    (sum_conj_tensor_swapLeft (fun s : c × a × b => x (s.2.1, s.2.2, s.1))
      (fun s : c × a × b => y (s.2.1, s.2.2, s.1)))

theorem ptraceR_ketBra_regroup₃ (x y : a × b × c → ℂ) :
    ptraceR (ketBra (fun s : c × a × b => x (s.2.1, s.2.2, s.1))
      (fun s : c × a × b => y (s.2.1, s.2.2, s.1))) = ptrace₁₂ (ketBra x y) := by
  ext k k'
  simp only [ptrace₁₂, ptraceR, Fintype.sum_prod_type]
  first | done | rfl

theorem sum_tensorVec_swap₁₂ (x y : a × b × c → ℂ) :
    ∑ p, conj (tensorVec x y (siteSwap₂ (siteSwap₁ p))) * tensorVec x y p =
      ((frobSq (ptrace₁₂ (ketBra x y)) : ℝ) : ℂ) := by
  rw [← ptraceR_ketBra_regroup₃]
  exact (Fintype.sum_equiv
    (Equiv.prodCongr (siteEquiv₃ : c × a × b ≃ a × b × c) (siteEquiv₃ : c × a × b ≃ a × b × c))
    (fun q : (c × a × b) × (c × a × b) =>
      conj (x (q.2.2.1, q.2.2.2, q.1.1) * y (q.1.2.1, q.1.2.2, q.2.1)) *
        (x (q.1.2.1, q.1.2.2, q.1.1) * y (q.2.2.1, q.2.2.2, q.2.1)))
    (fun p => conj (tensorVec x y (siteSwap₂ (siteSwap₁ p))) * tensorVec x y p)
    (fun _ => rfl)).symm.trans
    (sum_conj_tensor_swapRight (fun s : c × a × b => x (s.2.1, s.2.2, s.1))
      (fun s : c × a × b => y (s.2.1, s.2.2, s.1)))

/-! ### The seven nonnegative defects `⟨w, ∏_{i ∈ S} (1 - Fᵢ) w⟩`, `S ≠ ∅` -/

theorem rankOne_defect₁ (x y : a × b × c → ℂ) :
    0 ≤ vecNormSq x * vecNormSq y - frobSq (ptrace₁ (ketBra x y)) := by
  have h1 : ∑ p, conj (swapAnti siteSwap₁ (tensorVec x y) p) *
        swapAnti siteSwap₁ (tensorVec x y) p =
      ((2 : ℝ) : ℂ) * ∑ p, conj (swapAnti siteSwap₁ (tensorVec x y) p) * tensorVec x y p := by
    rw [sum_conj_swapAnti1_self siteSwap₁ siteSwap₁_invol (tensorVec x y)]
    norm_num
  have h2 : ∑ p, conj (swapAnti siteSwap₁ (tensorVec x y) p) * tensorVec x y p =
      ((vecNormSq x * vecNormSq y - frobSq (ptrace₁ (ketBra x y)) : ℝ) : ℂ) := by
    rw [sum_conj_swapAnti1_mul, sum_tensorVec_self, sum_tensorVec_swap₁, Complex.ofReal_sub]
  exact nonneg_of_sum_conj_eq _ _ 2 _ (by norm_num) h1 h2

theorem rankOne_defect₂ (x y : a × b × c → ℂ) :
    0 ≤ vecNormSq x * vecNormSq y - frobSq (ptrace₂ (ketBra x y)) := by
  have h1 : ∑ p, conj (swapAnti siteSwap₂ (tensorVec x y) p) *
        swapAnti siteSwap₂ (tensorVec x y) p =
      ((2 : ℝ) : ℂ) * ∑ p, conj (swapAnti siteSwap₂ (tensorVec x y) p) * tensorVec x y p := by
    rw [sum_conj_swapAnti1_self siteSwap₂ siteSwap₂_invol (tensorVec x y)]
    norm_num
  have h2 : ∑ p, conj (swapAnti siteSwap₂ (tensorVec x y) p) * tensorVec x y p =
      ((vecNormSq x * vecNormSq y - frobSq (ptrace₂ (ketBra x y)) : ℝ) : ℂ) := by
    rw [sum_conj_swapAnti1_mul, sum_tensorVec_self, sum_tensorVec_swap₂, Complex.ofReal_sub]
  exact nonneg_of_sum_conj_eq _ _ 2 _ (by norm_num) h1 h2

theorem rankOne_defect₃ (x y : a × b × c → ℂ) :
    0 ≤ vecNormSq x * vecNormSq y - frobSq (ptrace₃ (ketBra x y)) := by
  have h1 : ∑ p, conj (swapAnti siteSwap₃ (tensorVec x y) p) *
        swapAnti siteSwap₃ (tensorVec x y) p =
      ((2 : ℝ) : ℂ) * ∑ p, conj (swapAnti siteSwap₃ (tensorVec x y) p) * tensorVec x y p := by
    rw [sum_conj_swapAnti1_self siteSwap₃ siteSwap₃_invol (tensorVec x y)]
    norm_num
  have h2 : ∑ p, conj (swapAnti siteSwap₃ (tensorVec x y) p) * tensorVec x y p =
      ((vecNormSq x * vecNormSq y - frobSq (ptrace₃ (ketBra x y)) : ℝ) : ℂ) := by
    rw [sum_conj_swapAnti1_mul, sum_tensorVec_self, sum_tensorVec_swap₃, Complex.ofReal_sub]
  exact nonneg_of_sum_conj_eq _ _ 2 _ (by norm_num) h1 h2

theorem rankOne_defect₁₂ (x y : a × b × c → ℂ) :
    0 ≤ vecNormSq x * vecNormSq y - frobSq (ptrace₂ (ketBra x y)) -
      frobSq (ptrace₁ (ketBra x y)) + frobSq (ptrace₁₂ (ketBra x y)) := by
  have h1 : ∑ p, conj (swapAnti siteSwap₁ (swapAnti siteSwap₂ (tensorVec x y)) p) *
        swapAnti siteSwap₁ (swapAnti siteSwap₂ (tensorVec x y)) p =
      ((4 : ℝ) : ℂ) * ∑ p, conj (swapAnti siteSwap₁ (swapAnti siteSwap₂ (tensorVec x y)) p) *
        tensorVec x y p := by
    rw [sum_conj_swapAnti2_self siteSwap₁ siteSwap₂ siteSwap₁_invol siteSwap₂_invol
      siteSwap₁₂_comm (tensorVec x y)]
    norm_num
  have h2 : ∑ p, conj (swapAnti siteSwap₁ (swapAnti siteSwap₂ (tensorVec x y)) p) *
        tensorVec x y p =
      ((vecNormSq x * vecNormSq y - frobSq (ptrace₂ (ketBra x y)) -
        frobSq (ptrace₁ (ketBra x y)) + frobSq (ptrace₁₂ (ketBra x y)) : ℝ) : ℂ) := by
    rw [sum_conj_swapAnti2_mul, sum_tensorVec_self, sum_tensorVec_swap₂, sum_tensorVec_swap₁,
      sum_tensorVec_swap₁₂]
    simp only [Complex.ofReal_sub, Complex.ofReal_add]
  exact nonneg_of_sum_conj_eq _ _ 4 _ (by norm_num) h1 h2

theorem rankOne_defect₁₃ (x y : a × b × c → ℂ) :
    0 ≤ vecNormSq x * vecNormSq y - frobSq (ptrace₃ (ketBra x y)) -
      frobSq (ptrace₁ (ketBra x y)) + frobSq (ptrace₁₃ (ketBra x y)) := by
  have h1 : ∑ p, conj (swapAnti siteSwap₁ (swapAnti siteSwap₃ (tensorVec x y)) p) *
        swapAnti siteSwap₁ (swapAnti siteSwap₃ (tensorVec x y)) p =
      ((4 : ℝ) : ℂ) * ∑ p, conj (swapAnti siteSwap₁ (swapAnti siteSwap₃ (tensorVec x y)) p) *
        tensorVec x y p := by
    rw [sum_conj_swapAnti2_self siteSwap₁ siteSwap₃ siteSwap₁_invol siteSwap₃_invol
      siteSwap₁₃_comm (tensorVec x y)]
    norm_num
  have h2 : ∑ p, conj (swapAnti siteSwap₁ (swapAnti siteSwap₃ (tensorVec x y)) p) *
        tensorVec x y p =
      ((vecNormSq x * vecNormSq y - frobSq (ptrace₃ (ketBra x y)) -
        frobSq (ptrace₁ (ketBra x y)) + frobSq (ptrace₁₃ (ketBra x y)) : ℝ) : ℂ) := by
    rw [sum_conj_swapAnti2_mul, sum_tensorVec_self, sum_tensorVec_swap₃, sum_tensorVec_swap₁,
      sum_tensorVec_swap₁₃]
    simp only [Complex.ofReal_sub, Complex.ofReal_add]
  exact nonneg_of_sum_conj_eq _ _ 4 _ (by norm_num) h1 h2

theorem rankOne_defect₂₃ (x y : a × b × c → ℂ) :
    0 ≤ vecNormSq x * vecNormSq y - frobSq (ptrace₃ (ketBra x y)) -
      frobSq (ptrace₂ (ketBra x y)) + frobSq (ptrace₂₃ (ketBra x y)) := by
  have h1 : ∑ p, conj (swapAnti siteSwap₂ (swapAnti siteSwap₃ (tensorVec x y)) p) *
        swapAnti siteSwap₂ (swapAnti siteSwap₃ (tensorVec x y)) p =
      ((4 : ℝ) : ℂ) * ∑ p, conj (swapAnti siteSwap₂ (swapAnti siteSwap₃ (tensorVec x y)) p) *
        tensorVec x y p := by
    rw [sum_conj_swapAnti2_self siteSwap₂ siteSwap₃ siteSwap₂_invol siteSwap₃_invol
      siteSwap₂₃_comm (tensorVec x y)]
    norm_num
  have h2 : ∑ p, conj (swapAnti siteSwap₂ (swapAnti siteSwap₃ (tensorVec x y)) p) *
        tensorVec x y p =
      ((vecNormSq x * vecNormSq y - frobSq (ptrace₃ (ketBra x y)) -
        frobSq (ptrace₂ (ketBra x y)) + frobSq (ptrace₂₃ (ketBra x y)) : ℝ) : ℂ) := by
    rw [sum_conj_swapAnti2_mul, sum_tensorVec_self, sum_tensorVec_swap₃, sum_tensorVec_swap₂,
      sum_tensorVec_swap₂₃]
    simp only [Complex.ofReal_sub, Complex.ofReal_add]
  exact nonneg_of_sum_conj_eq _ _ 4 _ (by norm_num) h1 h2

theorem rankOne_defect₁₂₃ (x y : a × b × c → ℂ) :
    0 ≤ vecNormSq x * vecNormSq y - frobSq (ptrace₃ (ketBra x y)) -
      frobSq (ptrace₂ (ketBra x y)) + frobSq (ptrace₂₃ (ketBra x y)) -
      frobSq (ptrace₁ (ketBra x y)) + frobSq (ptrace₁₃ (ketBra x y)) +
      frobSq (ptrace₁₂ (ketBra x y)) - Complex.normSq (ketBra x y).trace := by
  have h1 : ∑ p, conj (swapAnti siteSwap₁ (swapAnti siteSwap₂
          (swapAnti siteSwap₃ (tensorVec x y))) p) *
        swapAnti siteSwap₁ (swapAnti siteSwap₂ (swapAnti siteSwap₃ (tensorVec x y))) p =
      ((8 : ℝ) : ℂ) * ∑ p, conj (swapAnti siteSwap₁ (swapAnti siteSwap₂
          (swapAnti siteSwap₃ (tensorVec x y))) p) * tensorVec x y p := by
    rw [sum_conj_swapAnti3_self siteSwap₁ siteSwap₂ siteSwap₃ siteSwap₁_invol siteSwap₂_invol
      siteSwap₃_invol siteSwap₁₂_comm siteSwap₁₃_comm siteSwap₂₃_comm (tensorVec x y)]
    norm_num
  have h2 : ∑ p, conj (swapAnti siteSwap₁ (swapAnti siteSwap₂
          (swapAnti siteSwap₃ (tensorVec x y))) p) * tensorVec x y p =
      ((vecNormSq x * vecNormSq y - frobSq (ptrace₃ (ketBra x y)) -
        frobSq (ptrace₂ (ketBra x y)) + frobSq (ptrace₂₃ (ketBra x y)) -
        frobSq (ptrace₁ (ketBra x y)) + frobSq (ptrace₁₃ (ketBra x y)) +
        frobSq (ptrace₁₂ (ketBra x y)) - Complex.normSq (ketBra x y).trace : ℝ) : ℂ) := by
    rw [sum_conj_swapAnti3_mul, sum_tensorVec_self, sum_tensorVec_swap₃, sum_tensorVec_swap₂,
      sum_tensorVec_swap₂₃, sum_tensorVec_swap₁, sum_tensorVec_swap₁₃, sum_tensorVec_swap₁₂,
      sum_tensorVec_swap₁₂₃]
    simp only [Complex.ofReal_sub, Complex.ofReal_add]
  exact nonneg_of_sum_conj_eq _ _ 8 _ (by norm_num) h1 h2

end SiteSwaps

/-- Manuscript Section 5.1: for a rank-one matrix `C = x y†`, `q(C) ≥ ‖x‖² ‖y‖² / 8`. -/
theorem endpointEnergy_ketBra_ge {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    (x y : a × b × c → ℂ) :
    vecNormSq x * vecNormSq y / 8 ≤ endpointEnergy (ketBra x y) := by
  have d1 := rankOne_defect₁ x y
  have d2 := rankOne_defect₂ x y
  have d3 := rankOne_defect₃ x y
  have d12 := rankOne_defect₁₂ x y
  have d13 := rankOne_defect₁₃ x y
  have d23 := rankOne_defect₂₃ x y
  have d123 := rankOne_defect₁₂₃ x y
  have hq : endpointEnergy (ketBra x y) = invN (ketBra x y) - invA (ketBra x y) / 2 +
      invB (ketBra x y) / 4 - invT (ketBra x y) / 8 := by
    unfold endpointEnergy energy
    ring
  have hN : invN (ketBra x y) = vecNormSq x * vecNormSq y := frobSq_ketBra_vecNormSq x y
  have hA : invA (ketBra x y) = frobSq (ptrace₁ (ketBra x y)) +
      frobSq (ptrace₂ (ketBra x y)) + frobSq (ptrace₃ (ketBra x y)) := rfl
  have hB : invB (ketBra x y) = frobSq (ptrace₁₂ (ketBra x y)) +
      frobSq (ptrace₁₃ (ketBra x y)) + frobSq (ptrace₂₃ (ketBra x y)) := rfl
  have hT : invT (ketBra x y) = Complex.normSq (ketBra x y).trace := rfl
  rw [hq, hN, hA, hB, hT]
  linarith

theorem matrix_eq_zero_of_frobSq_eq_zero {m n : Type*} [Fintype m] [Fintype n]
    (M : Matrix m n ℂ) (h : frobSq M = 0) : M = 0 := by
  unfold frobSq at h
  have h1 : ∀ i ∈ (Finset.univ : Finset m), ∑ j, Complex.normSq (M i j) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => Complex.normSq_nonneg (M i j)).mp h
  ext i j
  have h2 : ∀ j ∈ (Finset.univ : Finset n), Complex.normSq (M i j) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun j _ => Complex.normSq_nonneg (M i j)).mp
      (h1 i (Finset.mem_univ i))
  exact Complex.normSq_eq_zero.mp (h2 j (Finset.mem_univ j))

/-- A complex matrix of rank at most one is a ket-bra `u v†`. -/
theorem exists_eq_ketBra_of_rank_le_one {n : Type*} [Fintype n] (C : Matrix n n ℂ)
    (h : C.rank ≤ 1) : ∃ u v : n → ℂ, C = ketBra u v := by
  obtain ⟨X, B, hXB⟩ := (rank_le_iff_exists_mul C 1).mp h
  refine ⟨fun p => X p 0, fun q => conj (B 0 q), ?_⟩
  rw [hXB]
  ext p q
  simp only [ketBra, Matrix.mul_apply, Fin.sum_univ_one, starRingEnd_self_apply]

/-- Manuscript Section 5.1: an endpoint zero of rank at most one is zero. -/
theorem eq_zero_of_rank_le_one_of_endpointEnergy_eq_zero {a b c : Type*} [Fintype a] [Fintype b]
    [Fintype c] [DecidableEq a] [DecidableEq b] [DecidableEq c]
    (C : Matrix (a × b × c) (a × b × c) ℂ) (h : C.rank ≤ 1) (h0 : endpointEnergy C = 0) :
    C = 0 := by
  obtain ⟨u, v, rfl⟩ := exists_eq_ketBra_of_rank_le_one C h
  have hge := endpointEnergy_ketBra_ge u v
  rw [h0] at hge
  have hu : 0 ≤ vecNormSq u := by
    unfold vecNormSq
    exact Finset.sum_nonneg fun p _ => Complex.normSq_nonneg _
  have hv : 0 ≤ vecNormSq v := by
    unfold vecNormSq
    exact Finset.sum_nonneg fun p _ => Complex.normSq_nonneg _
  have hprod : vecNormSq u * vecNormSq v = 0 :=
    le_antisymm (by linarith) (mul_nonneg hu hv)
  have hF : frobSq (ketBra u v) = 0 := by
    rw [frobSq_ketBra_vecNormSq]
    exact hprod
  exact matrix_eq_zero_of_frobSq_eq_zero (ketBra u v) hF

/-- Manuscript Section 5.1: every nonzero endpoint zero of rank at most two has rank two. -/
theorem rank_eq_two_of_endpointEnergy_eq_zero {a b c : Type*} [Fintype a] [Fintype b]
    [Fintype c] [DecidableEq a] [DecidableEq b] [DecidableEq c]
    (C : Matrix (a × b × c) (a × b × c) ℂ) (h : C.rank ≤ 2) (h0 : endpointEnergy C = 0)
    (hC : C ≠ 0) : C.rank = 2 := by
  have h1 : ¬ C.rank ≤ 1 := fun h1 =>
    hC (eq_zero_of_rank_le_one_of_endpointEnergy_eq_zero C h1 h0)
  omega

end ThreeCopyQutritWerner

end
