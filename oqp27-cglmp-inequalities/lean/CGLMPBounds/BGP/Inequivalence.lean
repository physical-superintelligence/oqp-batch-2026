module

public import CGLMPBounds.BGP.Facet
public import CGLMPBounds.CGLMP.SaturationCount

@[expose] public section


/-!
# Proposition G.1: inequivalence to CGLMP and to outcome-fusion liftings

Two facets related by relabelling settings, outcomes or parties have bijective sets of
deterministic saturators. The counts 72 and 80 rule out even an arbitrary bijection of
deterministic strategies preserving saturation, a stronger obstruction.

A nontrivial outcome fusion identifies two outcomes in at least one setting. Any functional
factoring through that fusion has twins: its value on deterministic strategies is unchanged
when those two outcomes are exchanged at that setting. Direct integer certificates below
show that (G.1) has no twins. The factorization theorem permits arbitrary target outcome
types and arbitrary functions on their deterministic strategies; it therefore also excludes
affine rescalings and additions of identities valid on the no-signalling affine hull.
-/

namespace CGLMPBounds

/-- Saturator counts are invariant under any bijection preserving saturation. -/
theorem card_saturators_equiv {α β : Type*} [Fintype α] [Fintype β]
    (f : α → ℝ) (g : β → ℝ) (a b : ℝ) (e : α ≃ β)
    (h : ∀ s, f s = a ↔ g (e s) = b) :
    (Finset.univ.filter (fun s => f s = a)).card =
      (Finset.univ.filter (fun s => g s = b)).card := by
  classical
  apply Finset.card_equiv e
  intro s
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using h s

/-- In particular, no relabelling can take the BGP facet to CGLMP₄. -/
theorem bgp_not_cglmp_four_spec :
    ¬ ∃ e : Strategy (Fin 4) (Fin 4) ≃ Strategy (ZMod 4) (ZMod 4),
      ∀ s, bgpFunctional (detTable s) = 0 ↔ cglmp 4 (detTable (e s)) = 2 := by
  rintro ⟨e, he⟩
  have h := card_saturators_equiv (fun s => bgpFunctional (detTable s))
    (fun s => cglmp 4 (detTable s)) 0 2 e he
  rw [bgp_deterministic_values_spec.2.1, cglmp_four_saturation_count_spec.1] at h
  norm_num at h

/-- For every Alice setting and pair of distinct outcomes, another deterministic assignment
distinguishes them in the integer functional. This is an exact finite kernel certificate. -/
theorem bgp_no_twins_alice_int : ∀ x : Fin 2, ∀ a a' : Fin 4, a ≠ a' →
    ∃ s : Strategy (Fin 4) (Fin 4),
      bgpDetVal (Function.update s.1 x a, s.2) ≠
        bgpDetVal (Function.update s.1 x a', s.2) := by
  decide +kernel

/-- The corresponding exact certificate for Bob's settings. -/
theorem bgp_no_twins_bob_int : ∀ y : Fin 2, ∀ b b' : Fin 4, b ≠ b' →
    ∃ s : Strategy (Fin 4) (Fin 4),
      bgpDetVal (s.1, Function.update s.2 y b) ≠
        bgpDetVal (s.1, Function.update s.2 y b') := by
  decide +kernel

theorem bgp_no_twins_alice (x : Fin 2) (a a' : Fin 4) (ha : a ≠ a') :
    ∃ s : Strategy (Fin 4) (Fin 4),
      bgpFunctional (detTable (Function.update s.1 x a, s.2)) ≠
        bgpFunctional (detTable (Function.update s.1 x a', s.2)) := by
  obtain ⟨s, hs⟩ := bgp_no_twins_alice_int x a a' ha
  refine ⟨s, ?_⟩
  simpa only [bgpFunctional_detTable, ne_eq, Int.cast_inj] using hs

theorem bgp_no_twins_bob (y : Fin 2) (b b' : Fin 4) (hb : b ≠ b') :
    ∃ s : Strategy (Fin 4) (Fin 4),
      bgpFunctional (detTable (s.1, Function.update s.2 y b)) ≠
        bgpFunctional (detTable (s.1, Function.update s.2 y b')) := by
  obtain ⟨s, hs⟩ := bgp_no_twins_bob_int y b b' hb
  refine ⟨s, ?_⟩
  simpa only [bgpFunctional_detTable, ne_eq, Int.cast_inj] using hs

/-- The BGP functional cannot factor through any outcome map that identifies distinct outcomes
in even one setting. This includes every nontrivial outcome-fusion lifting. -/
theorem bgp_no_fusion_spec {α β : Type*}
    (fA : Fin 2 → Fin 4 → α) (fB : Fin 2 → Fin 4 → β)
    (hf : (∃ x, ¬ Function.Injective (fA x)) ∨ (∃ y, ¬ Function.Injective (fB y))) :
    ¬ ∃ G : Strategy α β → ℝ,
      ∀ s : Strategy (Fin 4) (Fin 4),
        bgpFunctional (detTable s) = G (fun x => fA x (s.1 x), fun y => fB y (s.2 y)) := by
  classical
  rintro ⟨G, hG⟩
  rcases hf with ⟨x, hx⟩ | ⟨y, hy⟩
  · obtain ⟨a, a', heq, hne⟩ : ∃ a a', fA x a = fA x a' ∧ a ≠ a' := by
      exact Function.not_injective_iff.mp hx
    obtain ⟨s, hs⟩ := bgp_no_twins_alice x a a' hne
    apply hs
    rw [hG, hG]
    congr 1
    apply Prod.ext
    · funext z
      by_cases hz : z = x
      · subst z
        simpa only [Function.update_self] using heq
      · simp [Function.update_of_ne hz]
    · rfl
  · obtain ⟨b, b', heq, hne⟩ : ∃ b b', fB y b = fB y b' ∧ b ≠ b' := by
      exact Function.not_injective_iff.mp hy
    obtain ⟨s, hs⟩ := bgp_no_twins_bob y b b' hne
    apply hs
    rw [hG, hG]
    congr 1
    apply Prod.ext
    · rfl
    · funext z
      by_cases hz : z = y
      · subst z
        simpa only [Function.update_self] using heq
      · simp [Function.update_of_ne hz]

end CGLMPBounds
