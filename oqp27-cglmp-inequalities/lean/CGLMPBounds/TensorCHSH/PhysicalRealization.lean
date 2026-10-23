module

public import CGLMPBounds.Statistics.TheoremA4
public import CGLMPBounds.CGLMP.FourierReducingRank

@[expose] public section


/-- Canonical supplement F.2 immediately before (F.5), and Theorem A.3:
    the four tracial settings (A0^T, B0, A1^T, B1) are complete rank-one PVMs
    on C^(2^m), with every m-bit outcome retained.  Both trace one and actual matrix rank one are exposed;
    IsPVM supplies Hermitian idempotent projections. -/
theorem _root_.CGLMPBounds.TensorCHSH.tensorProjectorFin_rankOnePVM_spec
    (m : ℕ) (t : Fin 4) :
    CGLMPBounds.IsPVM (CGLMPBounds.TensorCHSH.tensorProjectorFin m t.val) ∧
      (∀ a : Fin m → Bool,
        Matrix.trace (CGLMPBounds.TensorCHSH.tensorProjectorFin m t.val a) = (1 : ℂ)) ∧
      ∀ a : Fin m → Bool,
        (CGLMPBounds.TensorCHSH.tensorProjectorFin m t.val a).rank = 1 := by
  refine ⟨CGLMPBounds.TensorCHSH.tensorProjectorFin_isPVM m t.val,
    (fun a => CGLMPBounds.trace_tensorProjectorFin m t.val a), ?_⟩
  intro a
  have htrace := CGLMPBounds.trace_eq_rank_of_idempotent
    (CGLMPBounds.TensorCHSH.tensorProjectorFin m t.val a)
    ((CGLMPBounds.TensorCHSH.tensorProjectorFin_isPVM m t.val).mul_self a)
  have hcast : ((CGLMPBounds.TensorCHSH.tensorProjectorFin m t.val a).rank : ℂ) = 1 :=
    htrace.symm.trans (CGLMPBounds.trace_tensorProjectorFin m t.val a)
  exact_mod_cast hcast
