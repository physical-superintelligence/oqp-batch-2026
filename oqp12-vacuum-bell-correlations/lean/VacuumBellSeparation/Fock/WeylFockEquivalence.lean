module

public import VacuumBellSeparation.Fock.ExponentialTotality
public import VacuumBellSeparation.Weyl.Existence

@[expose] public section


/-!
# The constructed Weyl space is the literal symmetric Fock space

Normalized exponential vectors have precisely the Gaussian kernel.
The resulting RKHS completion map is onto by the proved exponential
vector totality in the actual symmetric Hilbert tensor direct sum.
-/

noncomputable section
namespace VacuumBellSeparation.Fock
open scoped InnerProductSpace ComplexConjugate

local instance weylFockEquivalenceSymmetricTensorComplete (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (n : ℕ) : CompleteSpace (SymmetricTensorPower E n) :=
  (isClosed_symmetricTensorSubmodule E n).isComplete.completeSpace_coe

local instance weylFockEquivalenceSymmetricFockComplete (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] :
    CompleteSpace (SymmetricFockSpace E) :=
  lp.completeSpace

set_option synthInstance.maxHeartbeats 200000

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def coherentVector (v : H) : SymmetricFockSpace H :=
  Complex.exp ((-(‖v‖ ^ 2 / 2) : ℝ) : ℂ) • exponentialVector H v

theorem inner_coherentVector (v w : H) :
    inner ℂ (coherentVector H v) (coherentVector H w) =
      weylKernel (id : H → H) v w := by
  rw [coherentVector, coherentVector, inner_smul_left, inner_smul_right,
    inner_exponentialVector, weylKernel_eq]
  simp only [id_eq]
  ring

theorem coherentVector_dense_span :
    (Submodule.span ℂ (Set.range (coherentVector H))).topologicalClosure = ⊤ := by
  have hs : Submodule.span ℂ (Set.range (exponentialVector H)) ≤
      Submodule.span ℂ (Set.range (coherentVector H)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨v, rfl⟩
    change exponentialVector H v ∈ Submodule.span ℂ (Set.range (coherentVector H))
    have h := Submodule.smul_mem (Submodule.span ℂ (Set.range (coherentVector H)))
      (Complex.exp ((-(‖v‖ ^ 2 / 2) : ℝ) : ℂ))⁻¹
      (Submodule.subset_span (Set.mem_range_self v))
    simpa only [coherentVector, smul_smul, inv_mul_cancel₀ (Complex.exp_ne_zero _),
      one_smul] using h
  have h := Submodule.topologicalClosure_mono hs
  rw [exponentialVector_dense_span H] at h
  exact top_unique h

def weylFockRealization₀ :
    RKHS.H₀ (weylRKHSKernel (id : H → H)) →ₗ[ℂ] SymmetricFockSpace H :=
  Finsupp.linearCombination ℂ (fun p : H × ℂ => p.2 • coherentVector H p.1)

@[simp] theorem weylFockRealization₀_single (z : H) (v a : ℂ) :
    weylFockRealization₀ H (Finsupp.single (z, v) a) =
      a • (v • coherentVector H z) := by simp [weylFockRealization₀]

theorem inner_weylFockRealization₀
    (f g : RKHS.H₀ (weylRKHSKernel (id : H → H))) :
    inner ℂ (weylFockRealization₀ H f) (weylFockRealization₀ H g) = inner ℂ f g := by
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero, inner_zero_left]
  | add f₁ f₂ h₁ h₂ => simp only [map_add, inner_add_left, h₁, h₂]
  | single p a =>
    induction g using Finsupp.induction_linear with
    | zero => simp only [map_zero, inner_zero_right]
    | add g₁ g₂ h₁ h₂ => simp only [map_add, inner_add_right, h₁, h₂]
    | single q b =>
      obtain ⟨z, v⟩ := p
      obtain ⟨w, u⟩ := q
      rw [weylFockRealization₀_single, weylFockRealization₀_single, inner_H₀_single]
      simp only [inner_smul_left, inner_smul_right, inner_coherentVector]
      ring

def weylFockRealization : WeylSpace (id : H → H) →ₗᵢ[ℂ] SymmetricFockSpace H :=
  ((weylFockRealization₀ H).isometryOfInner (inner_weylFockRealization₀ H)).fromCompletion

theorem weylFockRealization_weylVec (v : H) :
    weylFockRealization H (weylVec (id : H → H) v) = coherentVector H v := by
  rw [weylVec_def, weylFockRealization, LinearIsometry.fromCompletion_apply_coe]
  change weylFockRealization₀ H (Finsupp.single (v, 1) 1) = coherentVector H v
  simp

theorem weylFockRealization_surjective : Function.Surjective (weylFockRealization H) := by
  have hclosed : IsClosed (Set.range (weylFockRealization H)) :=
    (weylFockRealization H).isometry.isClosedEmbedding.isClosed_range
  have hspan : Submodule.span ℂ (Set.range (coherentVector H)) ≤
      (weylFockRealization H).toLinearMap.range := by
    apply Submodule.span_le.mpr
    rintro _ ⟨v, rfl⟩
    exact ⟨weylVec (id : H → H) v, weylFockRealization_weylVec H v⟩
  have h := (Submodule.span ℂ (Set.range (coherentVector H))).topologicalClosure_minimal
    hspan hclosed
  rw [coherentVector_dense_span H] at h
  exact LinearMap.range_eq_top.mp (top_unique h)

/-- A genuine unitary onto the full literal symmetric Fock space. -/
def weylFockEquiv : WeylSpace (id : H → H) ≃ₗᵢ[ℂ] SymmetricFockSpace H :=
  LinearIsometryEquiv.ofSurjective (weylFockRealization H) (weylFockRealization_surjective H)

@[simp] theorem weylFockEquiv_weylVec (v : H) :
    weylFockEquiv H (weylVec (id : H → H) v) = coherentVector H v :=
  weylFockRealization_weylVec H v

def fockWeyl (v : H) : SymmetricFockSpace H →L[ℂ] SymmetricFockSpace H :=
  (weylFockEquiv H).conjStarAlgEquiv (weylCLM (id : H → H) (fun _ _ => rfl) v)

theorem fockWeyl_coherentVector (v w : H) :
    fockWeyl H v (coherentVector H w) =
      weylPhase (id : H → H) v w • coherentVector H (v + w) := by
  rw [← weylFockEquiv_weylVec H w, fockWeyl,
    LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, LinearIsometryEquiv.symm_apply_apply,
    weylCLM_apply, weylOp_weylVec, map_smul, weylFockEquiv_weylVec]

theorem fockWeyl_mem_unitary (v : H) :
    fockWeyl H v ∈ unitary (SymmetricFockSpace H →L[ℂ] SymmetricFockSpace H) := by
  exact Unitary.map_mem (weylFockEquiv H).conjStarAlgEquiv
    (weylCLM_mem_unitary (id : H → H) (fun _ _ => rfl) v)

theorem fockWeyl_mul (v w : H) :
    fockWeyl H v * fockWeyl H w =
      weylPhase (id : H → H) v w • fockWeyl H (v + w) := by
  rw [fockWeyl, fockWeyl, ← map_mul, weylCLM_mul, map_smul]
  rfl

end VacuumBellSeparation.Fock
