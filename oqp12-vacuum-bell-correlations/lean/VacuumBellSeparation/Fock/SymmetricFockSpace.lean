module

public import VacuumBellSeparation.Fock.TensorPermutations
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Topology.Algebra.Module.ClosedSubmodule
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Exponential

@[expose] public section


/-!
# The literal symmetric Fock space and its exponential vectors

The n-particle space consists of the fixed points of all permutation
unitaries in the actual completed n-fold Hilbert tensor product. Their
Hilbert direct sum is symmetric Fock space. The exponential vectors are
the literal tensor series v^tensor_n / sqrt(n!), with the exact exp-inner
kernel. Density of their span is a separate theorem.
-/

noncomputable section
namespace VacuumBellSeparation.Fock
open scoped TensorProduct InnerProductSpace ENNReal ComplexConjugate

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def symmetricTensorSubmodule (n : ℕ) : Submodule ℂ (HilbertTensorPower H n) where
  carrier := {x | ∀ e : Equiv.Perm (Fin n), tensorPermutation H n e x = x}
  zero_mem' := by intro e; exact map_zero _
  add_mem' := by intro x y hx hy e; rw [map_add, hx e, hy e]
  smul_mem' := by intro c x hx e; rw [map_smul, hx e]

theorem isClosed_symmetricTensorSubmodule (n : ℕ) :
    IsClosed (symmetricTensorSubmodule H n : Set (HilbertTensorPower H n)) := by
  change IsClosed {x | ∀ e : Equiv.Perm (Fin n), tensorPermutation H n e x = x}
  simp only [Set.setOf_forall]
  exact isClosed_iInter fun e => isClosed_eq (tensorPermutation H n e).continuous continuous_id

def symmetricTensorClosedSubmodule (n : ℕ) : ClosedSubmodule ℂ (HilbertTensorPower H n) :=
  ⟨symmetricTensorSubmodule H n, isClosed_symmetricTensorSubmodule H n⟩

abbrev SymmetricTensorPower (n : ℕ) : Type _ := symmetricTensorClosedSubmodule H n

def pureSymmetricTensor (n : ℕ) (v : H) : SymmetricTensorPower H n :=
  ⟨tensorVector H n (fun _ => v), fun e => tensorPermutation_diagonal H n e v⟩

theorem inner_pureSymmetricTensor (n : ℕ) (v w : H) :
    inner ℂ (pureSymmetricTensor H n v) (pureSymmetricTensor H n w) = inner ℂ v w ^ n :=
  inner_tensorVector_diagonal H n v w

theorem norm_pureSymmetricTensor_sq (n : ℕ) (v : H) :
    ‖pureSymmetricTensor H n v‖ ^ 2 = (‖v‖ ^ 2) ^ n := by
  rw [@norm_sq_eq_re_inner ℂ, inner_pureSymmetricTensor, inner_self_eq_norm_sq_to_K]
  change (((‖v‖ : ℂ) ^ 2) ^ n).re = (‖v‖ ^ 2) ^ n
  simp only [← Complex.ofReal_pow, Complex.ofReal_re]

/-- The Hilbert direct sum of the actual symmetric tensor sectors. -/
abbrev SymmetricFockSpace : Type _ := lp (fun n : ℕ => SymmetricTensorPower H n) 2

def exponentialComponent (v : H) (n : ℕ) : SymmetricTensorPower H n :=
  (Real.sqrt (n.factorial : ℝ) : ℂ)⁻¹ • pureSymmetricTensor H n v

theorem norm_exponentialComponent_sq (v : H) (n : ℕ) :
    ‖exponentialComponent H v n‖ ^ 2 = (‖v‖ ^ 2) ^ n / (n.factorial : ℝ) := by
  rw [exponentialComponent, norm_smul, norm_inv,
    Complex.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow, inv_pow,
    Real.sq_sqrt (Nat.cast_nonneg _), norm_pureSymmetricTensor_sq, div_eq_mul_inv, mul_comm]

theorem exponentialComponent_memℓp (v : H) : Memℓp (exponentialComponent H v) 2 := by
  apply (memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).mpr
  have hs : Summable (fun n => ‖exponentialComponent H v n‖ ^ 2) := by
    simpa only [norm_exponentialComponent_sq] using Real.summable_pow_div_factorial (‖v‖ ^ 2)
  simpa [Real.rpow_two] using hs

def exponentialVector (v : H) : SymmetricFockSpace H :=
  ⟨exponentialComponent H v, exponentialComponent_memℓp H v⟩

theorem inner_exponentialComponent (v w : H) (n : ℕ) :
    inner ℂ (exponentialComponent H v n) (exponentialComponent H w n) =
      inner ℂ v w ^ n / (n.factorial : ℂ) := by
  have hden : (Real.sqrt (n.factorial : ℝ) : ℂ) ^ 2 = (n.factorial : ℂ) := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg n.factorial : 0 ≤ (n.factorial : ℝ))
  simp only [exponentialComponent, inner_smul_left, inner_smul_right, map_inv₀,
    Complex.conj_ofReal, inner_pureSymmetricTensor]
  rw [← mul_assoc, ← pow_two, inv_pow, hden]
  ring

theorem inner_exponentialVector (v w : H) :
    inner ℂ (exponentialVector H v) (exponentialVector H w) = Complex.exp (inner ℂ v w) := by
  rw [lp.inner_eq_tsum]
  change (∑' n, inner ℂ (exponentialComponent H v n) (exponentialComponent H w n)) = _
  simp_rw [inner_exponentialComponent]
  rw [Complex.exp_eq_exp_ℂ]
  exact (NormedSpace.expSeries_div_hasSum_exp (inner ℂ v w)).tsum_eq

theorem norm_exponentialVector_sq (v : H) :
    ‖exponentialVector H v‖ ^ 2 = Real.exp (‖v‖ ^ 2) := by
  rw [@norm_sq_eq_re_inner ℂ, inner_exponentialVector, inner_self_eq_norm_sq_to_K]
  change (Complex.exp ((‖v‖ : ℂ) ^ 2)).re = Real.exp (‖v‖ ^ 2)
  rw [← Complex.ofReal_pow, ← Complex.ofReal_exp, Complex.ofReal_re]

end VacuumBellSeparation.Fock
