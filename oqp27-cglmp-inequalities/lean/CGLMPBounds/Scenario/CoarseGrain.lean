module

public import CGLMPBounds.Noise.HalfNoise

@[expose] public section


/-!
# Coarse-graining of outcomes

Manuscript locator: Appendix F.2, text around (F.7): "Discarding all but the first `M` output bits
maps `T_m` to `T_M` and `u_{2^m}` to `u_{2^M}` ... Local behaviours remain local under this map.
Data processing and preservation of the noise mixture therefore give
`v_crit(T_m) ≤ v_crit(T_M)`."

For outcome maps `f : α → α'`, `g : β → β'`, the coarse-grained table is
`(coarseGrain f g q)(a',b'|x,y) = ∑_{f a = a', g b = b'} q(a,b|x,y)`, implemented entrywise as a
Bell functional so that linearity is inherited from `bell`.

* `coarseGrain_mem_localSet` : coarse-graining maps local tables to local tables;
* `critVisibility_le_coarseGrain` : if it maps the uniform table to the uniform table, the critical
  visibility cannot decrease.
-/

namespace CGLMPBounds

noncomputable section

variable {α β α' β' : Type*} [Fintype α] [Fintype β] [DecidableEq α'] [DecidableEq β']

/-- The coefficient table selecting the context `(x, y)` and the fibre over `(a', b')`. -/
def fibreTable (f : α → α') (g : β → β') (x y : Fin 2) (a' : α') (b' : β') : Table α β :=
  fun x₁ y₁ a b => if (x₁ = x ∧ y₁ = y) ∧ (a' = f a ∧ b' = g b) then 1 else 0

/-- Coarse-graining of outcomes along `f` and `g`:
`(coarseGrain f g q)(a',b'|x,y) = ∑_{f a = a', g b = b'} q(a,b|x,y)`. -/
def coarseGrain (f : α → α') (g : β → β') (q : Table α β) : Table α' β' :=
  fun x y a' b' => bell (fibreTable f g x y a' b') q

theorem coarseGrain_sum_smul {ι : Type*} (t : Finset ι) (w : ι → ℝ) (T : ι → Table α β)
    (f : α → α') (g : β → β') :
    coarseGrain f g (∑ i ∈ t, w i • T i) = ∑ i ∈ t, w i • coarseGrain f g (T i) := by
  funext x y a' b'
  simp only [coarseGrain, map_sum, map_smul, smul_eq_mul, Finset.sum_apply, Pi.smul_apply]

theorem coarseGrain_noisy [Fintype α'] [Fintype β'] (f : α → α') (g : β → β')
    (hu : coarseGrain f g (uniformTable α β) = uniformTable α' β') (v : ℝ) (q : Table α β) :
    coarseGrain f g (noisy v q) = noisy v (coarseGrain f g q) := by
  funext x y a' b'
  have hu' : bell (fibreTable f g x y a' b') (uniformTable α β) = uniformTable α' β' x y a' b' :=
    congrFun (congrFun (congrFun (congrFun hu x) y) a') b'
  simp only [noisy, coarseGrain, map_add, map_smul, smul_eq_mul, Pi.add_apply, Pi.smul_apply]
  rw [hu']

variable [DecidableEq α] [DecidableEq β]

theorem coarseGrain_detTable (f : α → α') (g : β → β') (s : Strategy α β) :
    coarseGrain f g (detTable s)
      = detTable ((fun x => f (s.1 x), fun y => g (s.2 y)) : Strategy α' β') := by
  funext x y a' b'
  show bell (fibreTable f g x y a' b') (detTable s) = _
  rw [bell_detTable]
  simp only [fibreTable, detTable]
  rw [Finset.sum_eq_single_of_mem x (Finset.mem_univ x)]
  · rw [Finset.sum_eq_single_of_mem y (Finset.mem_univ y)]
    · simp
    · intro y₁ _ hy
      simp [hy]
  · intro x₁ _ hx
    apply Finset.sum_eq_zero
    intro y₁ _
    simp [hx]

/-- Coarse-graining of outcomes preserves Bell locality. -/
theorem coarseGrain_mem_localSet (f : α → α') (g : β → β') {q : Table α β}
    (hq : q ∈ localSet α β) : coarseGrain f g q ∈ localSet α' β' := by
  obtain ⟨w, hw0, hw1, rfl⟩ := mem_localSet_iff.mp hq
  rw [coarseGrain_sum_smul]
  refine (convex_convexHull ℝ _).sum_mem (fun s _ => hw0 s) hw1 (fun s _ => ?_)
  rw [coarseGrain_detTable]
  exact subset_convexHull ℝ _ ⟨_, rfl⟩

/-- Abstract form of the visibility half of (F.7): a coarse-graining that maps uniform noise to
uniform noise cannot decrease the critical visibility. -/
theorem critVisibility_le_coarseGrain [Fintype α'] [Fintype β'] (f : α → α') (g : β → β')
    (hu : coarseGrain f g (uniformTable α β) = uniformTable α' β') (q : Table α β) :
    critVisibility q ≤ critVisibility (coarseGrain f g q) := by
  refine Real.sSup_le (fun v hv => ?_) (Real.sSup_nonneg (fun _ hw => hw.1))
  refine le_critVisibility hv.1 hv.2.1 ?_
  rw [← coarseGrain_noisy f g hu]
  exact coarseGrain_mem_localSet f g hv.2.2

end

end CGLMPBounds
