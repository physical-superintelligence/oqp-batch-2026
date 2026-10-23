module

public import ThreeCopyQutritWerner.CertificateX2Reduced

@[expose] public section


/-!
# Finite facts about the h images that the bridge consumes

On a canonical h type triple the residual Q-form is `πᵀ f π` with `π` the carrier action on the
ambient. The kinds argument (CertificateX2BridgeKinds, CertificateX2BridgeRank) needs, for every
h-block `b` with image `J_b`:

* the carrier fixes the image: `π_b J_b = J_b`;
* the kind projector fixes the image: `P_b J_b = J_b`;
* the dimension count: `trace (π_b P_b) = degree_b · r_b`;
* the block metric is nonsingular: `det H_b ≠ 0`;
* for the standard kind, `J_b` is fixed by the swap of the first two slots.

This module defines the objects (carrier action from per-site carrier data, slot permutations,
kind projectors) and the statement `X2ImageFacts`. The facts are finite and checkable by kernel
computation on the certificate data; nothing here is proved about them.
-/

noncomputable section

open scoped BigOperators Matrix Kronecker

namespace ThreeCopyQutritWerner

/-- Per-site carrier data: coefficient and h-frame action of each of the 120 carrier
permutations (the certificate's `projector` list of sector 0 and `A0_t`). -/
structure X2CarrierData where
  coeff : Fin 120 → ℚ
  act : Fin 120 → (t : Fin 8) → Matrix (Fin (x2Mult 0 t)) (Fin (x2Mult 0 t)) ℤ

/-- Carrier action on the ambient of an arrangement of h types. -/
def x2CarrierTriple (C : X2CarrierData) (t : Fin 3 → Fin 8) :
    Matrix (Fin (x2Mult 0 (t 0)) × Fin (x2Mult 0 (t 1)) × Fin (x2Mult 0 (t 2)))
      (Fin (x2Mult 0 (t 0)) × Fin (x2Mult 0 (t 1)) × Fin (x2Mult 0 (t 2))) ℚ :=
  ∑ j, C.coeff j • ((C.act j (t 0) ⊗ₖ (C.act j (t 1) ⊗ₖ C.act j (t 2))).map (Int.cast : ℤ → ℚ))

/-- Carrier action on the ambient of an h block. -/
def x2CarrierAmb (C : X2CarrierData) (b : x2Key 0) : Matrix (x2Amb 0 b) (x2Amb 0 b) ℚ :=
  x2CarrierTriple C (x2KeyTypes 0 b)

/-- Natural coordinates of an ambient point. -/
def x2AmbCoords (b : x2Key 0) (x : x2Amb 0 b) : Fin 3 → ℕ := ![(x.1 : ℕ), x.2.1, x.2.2]

/-- Slot permutation matrix on an h block's ambient: `(P_p v)(x) = v(x ∘ p)` (meaningful when
`p` preserves the block's types). -/
def x2SlotPerm (b : x2Key 0) (p : Fin 6) : Matrix (x2Amb 0 b) (x2Amb 0 b) ℚ :=
  Matrix.of fun x y => if x2AmbCoords b y = x2AmbCoords b x ∘ x2Perm3 p then 1 else 0

/-- Sign of a site permutation (index order of `x2Perm3`). -/
def x2Perm3Sign : Fin 6 → ℚ := ![1, -1, -1, 1, 1, -1]

/-- Position of the transposition of slots `i < j` in `x2Perm3`. -/
def x2Swap01Idx : Fin 6 := 2
def x2Swap12Idx : Fin 6 := 1
def x2Swap02Idx : Fin 6 := 5

/-- Kind projector of an h block on its ambient: S3 isotypic projectors for three equal types
(trivial, sign, standard), the symmetric/antisymmetric projector of the two equal slots, or the
identity for distinct types. -/
def x2KindProj (b : x2Key 0) : Matrix (x2Amb 0 b) (x2Amb 0 b) ℚ :=
  let t := x2KeyTypes 0 b
  let avg : Matrix (x2Amb 0 b) (x2Amb 0 b) ℚ := (1 / 6 : ℚ) • ∑ p, x2SlotPerm b p
  let alt : Matrix (x2Amb 0 b) (x2Amb 0 b) ℚ := (1 / 6 : ℚ) • ∑ p, x2Perm3Sign p • x2SlotPerm b p
  if t 0 = t 1 ∧ t 1 = t 2 then
    (if x2KeyKind 0 b = 0 then avg else if x2KeyKind 0 b = 1 then alt else 1 - avg - alt)
  else if t 0 = t 1 then
    (1 / 2 : ℚ) • (1 + (if x2KeyKind 0 b = 0 then 1 else -1 : ℚ) • x2SlotPerm b x2Swap01Idx)
  else if t 1 = t 2 then
    (1 / 2 : ℚ) • (1 + (if x2KeyKind 0 b = 0 then 1 else -1 : ℚ) • x2SlotPerm b x2Swap12Idx)
  else 1

/-- Rational image matrix of an h block. -/
def x2ImageQ (D : X2Data) (b : x2Key 0) : Matrix (x2Amb 0 b) (x2Col 0 b) ℚ :=
  (D.image 0 b).map (Int.cast : ℤ → ℚ)

/-- The finite image facts the bridge's kinds argument consumes. -/
structure X2ImageFacts (D : X2Data) (C : X2CarrierData) : Prop where
  carrier_fix : ∀ b : x2Key 0, x2CarrierAmb C b * x2ImageQ D b = x2ImageQ D b
  kind_fix : ∀ b : x2Key 0, x2KindProj b * x2ImageQ D b = x2ImageQ D b
  trace_count : ∀ b : x2Key 0,
    (x2CarrierAmb C b * x2KindProj b).trace = ((x2KeyDegree 0 b * x2KeySize 0 b : ℕ) : ℚ)
  metric_det : ∀ b : x2Key 0, (x2Metric D 0 b).det ≠ 0
  standard_swap : ∀ b : x2Key 0, x2KeyDegree 0 b = 2 →
    x2SlotPerm b x2Swap01Idx * x2ImageQ D b = x2ImageQ D b
  /-- Sorted h type triples with no block carry no carrier image. -/
  empty_triples : ∀ t : Fin 3 → Fin 8, t 0 ≤ t 1 → t 1 ≤ t 2 → t 2 < 7 →
    (∀ b : x2Key 0, x2KeyTypes 0 b ≠ t) → x2CarrierTriple C t = 0

end ThreeCopyQutritWerner

end
