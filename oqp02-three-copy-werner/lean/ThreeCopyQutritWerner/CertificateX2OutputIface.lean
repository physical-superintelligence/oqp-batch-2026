module

public import ThreeCopyQutritWerner.CertificateX2OutputBlock

@[expose] public section


/-!
# Output stage: the global table interface

`X2TableS`, `X2TableA` are the `transfer_slot` statements for a whole table (every pair with `type(j) ≤ type(k)`). `x2BlockIface_of_tables` derives the per-block interface
`X2BlockIface` consumed by `x2Out_eq_of_tables`, for every h block (all h type triples are sorted).
-/

namespace ThreeCopyQutritWerner
namespace X2

/-- The `S` table of a source sector agrees with `x2TransferS` (every pair `type(j) ≤ type(k)`). -/
def X2TableS (D : X2Data) (s : Fin 3) (Nsrc : X2Blocks s) (W : ℕ) (den : ℚ) (fib : ℕ → ℕ → ℕ) : Prop :=
  ∀ (t : Fin 8) (a b : ℕ) (j k : Fin 282), a < x2Mult 0 t → b < x2Mult 0 t →
    (x2SLabel 0 j).1 ≤ (x2SLabel 0 k).1 →
    x2TransferS D s Nsrc (x2SIdx 0 t a b) j k = (ent W (W - 1) (fib k j) (x2UOff0 t + a * x2Mult 0 t + b) : ℚ) / den

/-- The `A` table of a source sector agrees with `x2TransferA` (every pair `type(j) ≤ type(k)`). -/
def X2TableA (D : X2Data) (s : Fin 3) (Nsrc : X2Blocks s) (W : ℕ) (den : ℚ) (fib : ℕ → ℕ → ℕ) : Prop :=
  ∀ (t : Fin 8) (a b : ℕ) (j k : Fin 231), a < x2Mult 0 t → b < x2Mult 0 t →
    (x2ALabel 0 j).1 ≤ (x2ALabel 0 k).1 →
    x2TransferA D s Nsrc (x2SIdx 0 t a b) j k = (ent W (W - 1) (fib k j) (x2UOff0 t + a * x2Mult 0 t + b) : ℚ) / den

theorem x2SIdx_comm (s : Fin 3) (t : Fin 8) (a b : ℕ) : x2SIdx s t a b = x2SIdx s t b a := by
  apply Fin.ext
  simp only [x2SIdx]
  rw [min_comm, max_comm]

/-- The S label of a pair of type `t` has type `t`. -/
theorem x2SIdx_type : ∀ t : Fin 8, ∀ a < x2Mult 0 t, ∀ b < x2Mult 0 t, (x2SLabel 0 (x2SIdx 0 t a b)).1 = t := by
  decide +kernel

theorem x2AIdx_type_bool : ∀ t : Fin 8, ∀ a < x2Mult 0 t, ∀ b < x2Mult 0 t,
    (a == b || decide ((x2ALabel 0 (x2AIdx 0 t a b)).1 = t)) = true := by
  decide +kernel

/-- The A label of a pair `a ≠ b` of type `t` has type `t`. -/
theorem x2AIdx_type (t : Fin 8) (a b : ℕ) (ha : a < x2Mult 0 t) (hb : b < x2Mult 0 t) (hab : a ≠ b) :
    (x2ALabel 0 (x2AIdx 0 t a b)).1 = t := by
  have h := x2AIdx_type_bool t a ha b hb
  simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  rcases h with h | h
  · exact absurd h hab
  · exact h

/-- Every h block has sorted types. -/
theorem x2KeyTypes_sorted : ∀ b : x2Key 0, x2KeyTypes 0 b 0 ≤ x2KeyTypes 0 b 1 ∧ x2KeyTypes 0 b 1 ≤ x2KeyTypes 0 b 2 := by
  decide +kernel

theorem x2BlockIface_of_tables (D : X2Data) (s : Fin 3) (Nsrc : X2Blocks s) (b : x2Key 0) (W : ℕ) (den : ℚ)
    (fibS fibA : ℕ → ℕ → ℕ) (hS : X2TableS D s Nsrc W den fibS) (hA : X2TableA D s Nsrc W den fibA) :
    X2BlockIface D s Nsrc b W den fibS fibA := by
  obtain ⟨h01, h12⟩ := x2KeyTypes_sorted b
  have h02 := le_trans h01 h12
  refine ⟨fun x y => ?_, fun x y h1 h2 => ?_, fun x y h0 h2 => ?_, fun x y h0 h1 => ?_⟩
  · rw [x2SIdx_comm 0 (x2KeyTypes 0 b 0) x.1 y.1]
    exact hS _ _ _ _ _ y.1.isLt x.1.isLt (by
      rw [x2SIdx_type _ _ x.2.1.isLt _ y.2.1.isLt, x2SIdx_type _ _ x.2.2.isLt _ y.2.2.isLt]
      exact h12)
  · rw [x2SIdx_comm 0 (x2KeyTypes 0 b 0) x.1 y.1]
    exact hA _ _ _ _ _ y.1.isLt x.1.isLt (by
      rw [x2AIdx_type _ _ _ x.2.1.isLt y.2.1.isLt h1, x2AIdx_type _ _ _ x.2.2.isLt y.2.2.isLt h2]
      exact h12)
  · rw [x2SIdx_comm 0 (x2KeyTypes 0 b 1) x.2.1 y.2.1]
    exact hA _ _ _ _ _ y.2.1.isLt x.2.1.isLt (by
      rw [x2AIdx_type _ _ _ x.1.isLt y.1.isLt h0, x2AIdx_type _ _ _ x.2.2.isLt y.2.2.isLt h2]
      exact h02)
  · rw [x2SIdx_comm 0 (x2KeyTypes 0 b 2) x.2.2 y.2.2]
    exact hA _ _ _ _ _ y.2.2.isLt x.2.2.isLt (by
      rw [x2AIdx_type _ _ _ x.1.isLt y.1.isLt h0, x2AIdx_type _ _ _ x.2.1.isLt y.2.1.isLt h1]
      exact h01)

end X2
end ThreeCopyQutritWerner
