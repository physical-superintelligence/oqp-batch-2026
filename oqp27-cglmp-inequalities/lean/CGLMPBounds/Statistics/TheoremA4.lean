module

public import CGLMPBounds.Statistics.Supremum
public import CGLMPBounds.Defs.RankOnePVM

@[expose] public section


/-!
# Theorem A.4, projective part

Supplement, Theorem A.4: "For every fixed input distribution independent of the hidden variable,
`sup_{d ≥ 2, two rank-one PVMs per party on Φ_d} S_μ(q) = Ξ(μ)`."

The upper bound is Theorem F.2 (tracial PVM behaviours are no-signalling). The lower bound uses the
common-input tensor CHSH behaviours `T_m`, whose measurements are rank-one PVMs on `ℂ^{2^m}`
(`TensorCHSH/PVM.lean`), after relabelling the outcomes `Fin m → Bool` by `Fin (2^m)`, and
`sup_m S_μ(T_m) = Ξ(μ)` (`Statistics/Supremum.lean`).

* `coarseGrain_equiv_apply`, `statStrength_coarseGrain_equiv` : relabelling outcomes along
  bijections does not change `S_μ`;
* `trace_tensorProjectorFin` : the tensor CHSH projectors have trace one (rank one);
* `relabel_tensorCHSHTable_mem` : the relabelled `T_m` is a behaviour of two rank-one PVMs per party
  on `Φ_{2^m}`;
* `statistical_supremum_spec` : Theorem A.4, projective part.
-/

namespace CGLMPBounds

noncomputable section

open scoped ENNReal
open Finset

/-! ### Relabelling outcomes -/

theorem coarseGrain_equiv_apply {α β α' β' : Type*} [Fintype α] [Fintype β] [DecidableEq α']
    [DecidableEq β'] (e : α ≃ α') (f : β ≃ β') (T : Table α β) (x y : Fin 2) (a' : α') (b' : β') :
    coarseGrain e f T x y a' b' = T x y (e.symm a') (f.symm b') := by
  rw [TensorCHSH.coarseGrain_apply, Fintype.sum_eq_single (e.symm a')]
  · rw [Fintype.sum_eq_single (f.symm b')]
    · rw [if_pos ⟨(e.apply_symm_apply a').symm, (f.apply_symm_apply b').symm⟩]
    · intro b hb
      rw [if_neg]
      rintro ⟨-, h⟩
      exact hb (by rw [h, f.symm_apply_apply])
  · intro a ha
    refine Finset.sum_eq_zero (fun b _ => ?_)
    rw [if_neg]
    rintro ⟨h, -⟩
    exact ha (by rw [h, e.symm_apply_apply])

theorem coarseGrain_equiv_symm {α β α' β' : Type*} [Fintype α] [Fintype β] [Fintype α']
    [Fintype β'] [DecidableEq α] [DecidableEq β] [DecidableEq α'] [DecidableEq β'] (e : α ≃ α')
    (f : β ≃ β') (T : Table α β) : coarseGrain e.symm f.symm (coarseGrain e f T) = T := by
  funext x y a b
  rw [coarseGrain_equiv_apply, coarseGrain_equiv_apply, Equiv.symm_symm, Equiv.symm_symm,
    e.symm_apply_apply, f.symm_apply_apply]

/-- Relabelling the outcomes of both parties along bijections does not change `S_μ`. -/
theorem statStrength_coarseGrain_equiv {α β α' β' : Type*} [Fintype α] [Fintype β] [Fintype α']
    [Fintype β'] [DecidableEq α] [DecidableEq β] [DecidableEq α'] [DecidableEq β'] (e : α ≃ α')
    (f : β ≃ β') (μ : Fin 2 → Fin 2 → ℝ) {T : Table α β} (hT : ∀ x y a b, 0 ≤ T x y a b) :
    statStrength μ (coarseGrain e f T) = statStrength μ T := by
  refine le_antisymm (statStrength_coarseGrain_le e f μ hT) ?_
  have h := statStrength_coarseGrain_le e.symm f.symm μ (q := coarseGrain e f T)
    (fun x y a b => by rw [coarseGrain_equiv_apply]; exact hT _ _ _ _)
  rwa [coarseGrain_equiv_symm] at h

theorem isPVM_comp_equiv {n : ℕ} {α α' : Type*} [Fintype α] [Fintype α']
    {P : α → Matrix (Fin n) (Fin n) ℂ} (hP : IsPVM P) (e : α' ≃ α) :
    IsPVM (fun a' => P (e a')) where
  isHermitian a' := hP.isHermitian (e a')
  mul_self a' := hP.mul_self (e a')
  sum_eq_one := by
    rw [Equiv.sum_comp e P]
    exact hP.sum_eq_one

/-! ### The tensor CHSH projectors have rank one -/

theorem trace_qubitProjector (t : ℕ) (c : Bool) :
    Matrix.trace (TensorCHSH.qubitProjector t c) = 1 := by
  unfold TensorCHSH.qubitProjector
  rw [Matrix.trace_smul, Matrix.trace_add, Matrix.trace_one, Matrix.trace_smul,
    TensorCHSH.trace_chshObservable, smul_zero, add_zero, Fintype.card_fin]
  norm_num

theorem trace_tensorProjectorFin (m t : ℕ) (a : Fin m → Bool) :
    Matrix.trace (TensorCHSH.tensorProjectorFin m t a) = 1 := by
  have h1 : Matrix.trace (TensorCHSH.tensorProjectorFin m t a)
      = Matrix.trace (TensorCHSH.tensorProjector m t a) := by
    unfold TensorCHSH.tensorProjectorFin Matrix.trace
    simp only [Matrix.diag, Matrix.reindex_apply, Matrix.submatrix_apply]
    exact Fintype.sum_equiv finFunctionFinEquiv.symm _ _ (fun _ => rfl)
  rw [h1]
  unfold Matrix.trace
  simp only [Matrix.diag, TensorCHSH.tensorProjector, Matrix.of_apply]
  rw [← TensorCHSH.prod_sum_fin (fun j c => TensorCHSH.qubitProjector t (a j) c c)]
  exact Finset.prod_eq_one (fun j _ => trace_qubitProjector t (a j))

/-- The relabelling `(Fin m → Bool) ≃ Fin (2^m)` of `m`-bit outcomes. -/
def bitsEquiv (m : ℕ) : (Fin m → Bool) ≃ Fin (2 ^ m) :=
  (Equiv.arrowCongr (Equiv.refl (Fin m)) finTwoEquiv.symm).trans finFunctionFinEquiv

/-- The relabelled `T_m` is a behaviour of two rank-one PVMs per party on `Φ_{2^m}`. -/
theorem relabel_tensorCHSHTable_mem (m : ℕ) :
    coarseGrain (bitsEquiv m) (bitsEquiv m) (TensorCHSH.tensorCHSHTable m)
      ∈ rankOnePVMBehaviours (2 ^ m) := by
  refine ⟨fun x a' => TensorCHSH.tensorProjectorFin m (2 * x.val) ((bitsEquiv m).symm a'),
    fun y b' => TensorCHSH.tensorProjectorFin m (1 + 2 * y.val) ((bitsEquiv m).symm b'),
    fun x => ⟨isPVM_comp_equiv (TensorCHSH.tensorProjectorFin_isPVM m _) _,
      fun a' => trace_tensorProjectorFin m _ _⟩,
    fun y => ⟨isPVM_comp_equiv (TensorCHSH.tensorProjectorFin_isPVM m _) _,
      fun b' => trace_tensorProjectorFin m _ _⟩, ?_⟩
  funext x y a' b'
  rw [coarseGrain_equiv_apply]
  rfl

/-- **Theorem A.4, (A.7), projective part.** For every input law `μ`, the supremum of `S_μ` over
`d ≥ 2` and over the behaviours of two rank-one PVMs per party on `Φ_d` equals `Ξ(μ)`. -/
theorem statistical_supremum_spec {μ : Fin 2 → Fin 2 → ℝ} (hμ : ∀ x y, 0 ≤ μ x y)
    (hμ1 : ∑ x, ∑ y, μ x y = 1) :
    ⨆ (d : ℕ) (_ : 2 ≤ d) (q ∈ rankOnePVMBehaviours d), statStrength μ q = xiMin μ := by
  apply le_antisymm
  · refine iSup_le (fun d => iSup_le (fun hd => iSup₂_le (fun q hq => ?_)))
    obtain ⟨A, B, hA, hB, rfl⟩ := hq
    haveI : NeZero d := ⟨by omega⟩
    have hns := tracialTable_isNoSignalling (fun x => (hA x).1) (fun y => (hB y).1)
    exact (statistical_ceiling_spec hns hμ hμ1).1.trans (statistical_ceiling_spec hns hμ hμ1).2
  · rw [← iSup_statStrength_tensorCHSHTable hμ hμ1]
    refine iSup_le (fun m => ?_)
    have hmono : statStrength μ (TensorCHSH.tensorCHSHTable m)
        ≤ statStrength μ (TensorCHSH.tensorCHSHTable (m + 1)) := by
      rw [TensorCHSH.tensorCHSHTable_eq, TensorCHSH.tensorCHSHTable_eq]
      exact statStrength_tensorTable_succ_le μ m chshErrRate_pos.le chshErrRate_lt_one.le
    refine hmono.trans ?_
    have hT0 : ∀ x y a b, 0 ≤ TensorCHSH.tensorCHSHTable (m + 1) x y a b :=
      (TensorCHSH.tensorCHSHTable_isNoSignalling (m + 1)).isBehaviour.nonneg
    rw [← statStrength_coarseGrain_equiv (bitsEquiv (m + 1)) (bitsEquiv (m + 1)) μ hT0]
    have h2 : 2 ≤ 2 ^ (m + 1) := two_le_two_pow (by omega)
    exact le_iSup_of_le (2 ^ (m + 1)) (le_iSup_of_le h2
      (le_iSup₂_of_le _ (relabel_tensorCHSHTable_mem (m + 1)) le_rfl))

end

end CGLMPBounds
