module

public import ThreeCopyQutritWerner.CertificateX2BridgeFinal
public import ThreeCopyQutritWerner.CertificateX2BridgeTripleParts

@[expose] public section


/-!
# Triples of three equal types, and the bridge without extra hypotheses

On `(a, a, a)` the frame slot permutations are the S3 permutation matrices `x2S3Mat`, the kind
projectors are the trivial / sign / standard projectors, and the carrier, the endpoint target, the
metric and both transferred forms commute with all six permutations. With the four parts
`x2S3Part` (the standard projector split into its even and odd halves), the h-side form is
positive semidefinite from the triple's keys: the trivial and sign keys' images, the standard
key's image (even half) and its partner `(P₁₂ - P₀₂) J` (odd half, reduced block `3 Jᴴ f J`).

Still to write: `x2_hform_triple`, the application of
`x2_posSemidef_of_parts_complex` with the parts `x2S3Part` and the spanning matrices `x2TripleM`, which
discharges `htriple` of `x2_qutritEndpointInequality_of_facts`.
-/

noncomputable section

open scoped BigOperators Matrix Kronecker ComplexOrder

namespace ThreeCopyQutritWerner

/-! ## Frame objects on (a, a, a) -/

theorem x2FrameCoords_triple (a : Fin 7)
    (i : Fin (certificatePhysicalFrameSystem0.size a *
      (certificatePhysicalFrameSystem0.size a * certificatePhysicalFrameSystem0.size a))) :
    x2FrameCoords (a, a, a) i = fun k => (x2Coords3 _ i k : ℕ) := by
  funext k
  fin_cases k <;> rfl

theorem x2SlotPermFrame_triple (a : Fin 7) (q : Fin 6) :
    x2SlotPermFrame (a, a, a) q = x2S3Mat (certificatePhysicalFrameSystem0.size a) q := by
  ext i j
  simp only [x2SlotPermFrame, x2S3Mat, x2FunMat, Matrix.of_apply]
  rw [x2FrameCoords_triple, x2FrameCoords_triple]
  have key : ((fun k => (x2Coords3 _ j k : ℕ)) = (fun k => (x2Coords3 _ i k : ℕ)) ∘ x2Perm3 q) ↔
      x2SlotMap3 _ q i = j := by
    constructor
    · intro h
      have hc : x2Coords3 _ j = x2Coords3 _ i ∘ x2Perm3 q :=
        funext fun k => Fin.ext (congrFun h k)
      rw [x2SlotMap3, ← hc, x2Idx3_coords]
    · intro h
      rw [← h, x2SlotMap3, x2Coords3_idx]
      rfl
  by_cases h : x2SlotMap3 _ q i = j
  · rw [if_pos (key.mpr h), if_pos h]
  · rw [if_neg (fun h' => h (key.mp h')), if_neg h]

theorem x2KindProjFrame_triple (a : Fin 7) (k : ℕ) :
    x2KindProjFrame (a, a, a) k = if k = 0 then x2S3Avg (certificatePhysicalFrameSystem0.size a)
      else if k = 1 then x2S3Alt (certificatePhysicalFrameSystem0.size a)
      else x2S3Std (certificatePhysicalFrameSystem0.size a) := by
  unfold x2KindProjFrame
  simp only [and_self, if_true, x2SlotPermFrame_triple]
  rfl

/-! ## Invariance under the site permutations -/

theorem x2_tsa_triple_inv {n F T : Type*} [Fintype n] [Fintype F] [DecidableEq T]
    (s : CertificatePhysicalFrameSystem n F T)
    (A : (t : T) → Matrix (Fin (s.size t)) (Fin (s.size t)) ℂ) (a : T) (q : Fin 6)
    (i j : Fin (s.size a * (s.size a * s.size a))) :
    certificateTripleSourceAction s A A A (a, a, a) (x2SlotMap3 (s.size a) q i)
        (x2SlotMap3 (s.size a) q j) = certificateTripleSourceAction s A A A (a, a, a) i j := by
  rw [x2_tripleSourceAction_apply, x2_tripleSourceAction_apply]
  show A a (x2Coords3 _ (x2SlotMap3 _ q i) 0) (x2Coords3 _ (x2SlotMap3 _ q j) 0) *
      (A a (x2Coords3 _ (x2SlotMap3 _ q i) 1) (x2Coords3 _ (x2SlotMap3 _ q j) 1) *
        A a (x2Coords3 _ (x2SlotMap3 _ q i) 2) (x2Coords3 _ (x2SlotMap3 _ q j) 2)) =
    A a (x2Coords3 _ i 0) (x2Coords3 _ j 0) *
      (A a (x2Coords3 _ i 1) (x2Coords3 _ j 1) * A a (x2Coords3 _ i 2) (x2Coords3 _ j 2))
  simp only [x2SlotMap3, x2Coords3_idx, Function.comp_apply]
  fin_cases q <;> simp [x2Perm3] <;> first | ring1 | (ring_nf <;> simp)

theorem x2_carrier_triple_comm (a : Fin 7) (q : Fin 6) :
    certificateCarrierJointAction0 (a, a, a) * x2S3Mat (certificatePhysicalFrameSystem0.size a) q =
      x2S3Mat (certificatePhysicalFrameSystem0.size a) q * certificateCarrierJointAction0 (a, a, a) := by
  apply x2S3Mat_comm
  intro i j
  unfold certificateCarrierJointAction0
  simp only [Matrix.sum_apply, Matrix.smul_apply]
  apply Finset.sum_congr rfl
  intro p _
  rw [x2_tsa_triple_inv certificatePhysicalFrameSystem0 _ a q i j]

theorem x2_target_triple_comm (a : Fin 7) (q : Fin 6) :
    x2TargetQForm (a, a, a) * x2S3Mat (certificatePhysicalFrameSystem0.size a) q =
      x2S3Mat (certificatePhysicalFrameSystem0.size a) q * x2TargetQForm (a, a, a) := by
  apply x2S3Mat_comm
  intro i j
  unfold x2TargetQForm certificateThreeSiteFrameSystem0
  rw [x2_metric_tripleSourceAction]
  exact x2_tsa_triple_inv certificatePhysicalFrameSystem0 _ a q i j

theorem x2_metric_triple_comm (a : Fin 7) (q : Fin 6) :
    certificateThreeSiteFrameSystem0.metric (a, a, a) *
        x2S3Mat (certificatePhysicalFrameSystem0.size a) q =
      x2S3Mat (certificatePhysicalFrameSystem0.size a) q *
        certificateThreeSiteFrameSystem0.metric (a, a, a) := by
  apply x2S3Mat_comm
  intro i j
  exact x2_tsa_triple_inv certificatePhysicalFrameSystem0
    certificatePhysicalFrameSystem0.metric a q i j

/-- The transferred tensor is invariant under every permutation of its three unit arguments. -/
theorem x2_transferVec_perm (D : X2Data) (s : Fin 3) (N : X2Blocks s) (q : Fin 6)
    (u : Fin 3 → X2U 0) :
    ((x2Qu D s ⊗ₖ (x2Qu D s ⊗ₖ x2Qu D s)) *ᵥ x2FmVec D s N)
        (u (x2Perm3 q 0), u (x2Perm3 q 1), u (x2Perm3 q 2)) =
      ((x2Qu D s ⊗ₖ (x2Qu D s ⊗ₖ x2Qu D s)) *ᵥ x2FmVec D s N) (u 0, u 1, u 2) := by
  fin_cases q
  · rfl
  · exact x2_transferVec_swap12 D s N (u 0) (u 1) (u 2)
  · exact x2_transferVec_swap01 D s N (u 0) (u 1) (u 2)
  · exact (x2_transferVec_swap12 D s N (u 1) (u 0) (u 2)).trans
      (x2_transferVec_swap01 D s N (u 0) (u 1) (u 2))
  · exact (x2_transferVec_swap01 D s N (u 0) (u 2) (u 1)).trans
      (x2_transferVec_swap12 D s N (u 0) (u 1) (u 2))
  · exact (x2_transferVec_swap01 D s N (u 1) (u 2) (u 0)).trans
      ((x2_transferVec_swap12 D s N (u 1) (u 0) (u 2)).trans
        (x2_transferVec_swap01 D s N (u 0) (u 1) (u 2)))

theorem x2_transferQForm_triple_comm (D : X2Data) (s : Fin 3) (N : X2Blocks s) (a : Fin 7)
    (q : Fin 6) :
    x2TransferQForm D s N (a, a, a) * x2S3Mat (certificatePhysicalFrameSystem0.size a) q =
      x2S3Mat (certificatePhysicalFrameSystem0.size a) q * x2TransferQForm D s N (a, a, a) := by
  apply x2S3Mat_comm
  intro i j
  show ((((x2Qu D s ⊗ₖ (x2Qu D s ⊗ₖ x2Qu D s)) *ᵥ x2FmVec D s N)
      (x2UnitAt 0 certificatePhysicalFrameSystem0.size Fin.castSucc x2_size0 a
          (x2Coords3 _ (x2SlotMap3 _ q i) 0) (x2Coords3 _ (x2SlotMap3 _ q j) 0),
        x2UnitAt 0 certificatePhysicalFrameSystem0.size Fin.castSucc x2_size0 a
          (x2Coords3 _ (x2SlotMap3 _ q i) 1) (x2Coords3 _ (x2SlotMap3 _ q j) 1),
        x2UnitAt 0 certificatePhysicalFrameSystem0.size Fin.castSucc x2_size0 a
          (x2Coords3 _ (x2SlotMap3 _ q i) 2) (x2Coords3 _ (x2SlotMap3 _ q j) 2)) : ℚ) : ℂ) =
    ((((x2Qu D s ⊗ₖ (x2Qu D s ⊗ₖ x2Qu D s)) *ᵥ x2FmVec D s N)
      (x2UnitAt 0 certificatePhysicalFrameSystem0.size Fin.castSucc x2_size0 a
          (x2Coords3 _ i 0) (x2Coords3 _ j 0),
        x2UnitAt 0 certificatePhysicalFrameSystem0.size Fin.castSucc x2_size0 a
          (x2Coords3 _ i 1) (x2Coords3 _ j 1),
        x2UnitAt 0 certificatePhysicalFrameSystem0.size Fin.castSucc x2_size0 a
          (x2Coords3 _ i 2) (x2Coords3 _ j 2)) : ℚ) : ℂ)
  simp only [x2SlotMap3, x2Coords3_idx, Function.comp_apply]
  exact congrArg (fun z : ℚ => (z : ℂ)) (x2_transferVec_perm D s N q
    (fun k => x2UnitAt 0 certificatePhysicalFrameSystem0.size Fin.castSucc x2_size0 a
      (x2Coords3 _ i k) (x2Coords3 _ j k)))

/-! ## The four keyed parts on (a, a, a) -/

/-- Keys of a triple of three equal types have degree two exactly for the standard kind. -/
theorem x2_keyDegree_kind : ∀ b : x2Key 0,
    x2KeyDegree 0 b = if x2KeyKind 0 b = 2 then 2 else 1 := by
  decide +kernel

theorem x2_eq_zero_of_idempotent_trace_zero_complex {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℂ) (hP : P * P = P) (htr : P.trace = 0) : P = 0 := by
  obtain ⟨A, hA⟩ := x2_idempotent_eq_mul_of_trace_complex P hP (0 : Matrix n (Fin 0) ℂ)
    (by rw [Matrix.mul_zero]) (0 : Matrix (Fin 0) n ℂ) (by ext i j; exact Fin.elim0 i)
    (by rw [htr, Fintype.card_fin, Nat.cast_zero])
  rw [hA, Matrix.zero_mul]

theorem x2_trace_stdHalf {n : Type*} [Fintype n] [DecidableEq n] (π std S : Matrix n n ℂ)
    (b : Bool) :
    (π * (std * x2InvolutionPart S b)).trace =
      (1 / 2 : ℂ) * ((π * std).trace + (if b then (-1 : ℂ) else 1) * (π * (std * S)).trace) := by
  simp only [x2InvolutionPart, Matrix.mul_smul, Matrix.mul_add, Matrix.mul_one,
    Matrix.trace_smul, Matrix.trace_add, smul_eq_mul]

/-- The standard partner of an image on `(a, a, a)`. -/
def x2PartnerAt (D : X2Data) (a : Fin 7) (b : x2Key 0) :
    Matrix (Fin (certificatePhysicalFrameSystem0.size a *
      (certificatePhysicalFrameSystem0.size a * certificatePhysicalFrameSystem0.size a)))
      (x2Col 0 b) ℂ :=
  (x2S3Mat (certificatePhysicalFrameSystem0.size a) 1 -
    x2S3Mat (certificatePhysicalFrameSystem0.size a) 5) * x2ImageAt D (a, a, a) b

/-- The partner of an optional key. -/
def x2PartPartner (D : X2Data) (a : Fin 7) : (o : Option (x2Key 0)) →
    Matrix (Fin (certificatePhysicalFrameSystem0.size a *
      (certificatePhysicalFrameSystem0.size a * certificatePhysicalFrameSystem0.size a)))
      (x2PartCols o) ℂ
  | some b => x2PartnerAt D a b
  | none => 0

/-- The keys of the four parts (the standard key twice). -/
def x2TripleKeys (a : Fin 7) : Fin 4 → Option (x2Key 0) :=
  ![x2KeyOf (a, a, a) 0, x2KeyOf (a, a, a) 1, x2KeyOf (a, a, a) 2, x2KeyOf (a, a, a) 2]

/-- The spanning matrices of the four parts. -/
def x2TripleM (D : X2Data) (a : Fin 7) : (k : Fin 4) →
    Matrix (Fin (certificatePhysicalFrameSystem0.size a *
      (certificatePhysicalFrameSystem0.size a * certificatePhysicalFrameSystem0.size a)))
      (x2PartCols (x2TripleKeys a k)) ℂ
  | 0 => x2PartImage D (a, a, a) (x2KeyOf (a, a, a) 0)
  | 1 => x2PartImage D (a, a, a) (x2KeyOf (a, a, a) 1)
  | 2 => x2PartImage D (a, a, a) (x2KeyOf (a, a, a) 2)
  | 3 => x2PartPartner D a (x2KeyOf (a, a, a) 2)

/-- `J + P₁₂ J + P₀₂ J = 0` for an image in the even half of the standard component. -/
theorem x2_standard_relation (m : ℕ) {r : Type*} [Fintype r]
    (J : Matrix (Fin (m * (m * m))) r ℂ) (hstd : x2S3Std m * J = J) (hS : x2S3Swap m * J = J) :
    J + x2S3Mat m 1 * J + x2S3Mat m 5 * J = 0 := by
  have h0 : x2S3Avg m * J = 0 := by
    rw [← hstd, ← Matrix.mul_assoc, x2S3Avg_std, Matrix.zero_mul]
  have h3 : x2S3Mat m 3 * J = x2S3Mat m 5 * J := by
    rw [show x2S3Mat m 3 = x2S3Mat m 5 * x2S3Mat m 2 from (x2S3Mat_mul m 5 2).symm,
      Matrix.mul_assoc, show x2S3Mat m 2 = x2S3Swap m from rfl, hS]
  have h4 : x2S3Mat m 4 * J = x2S3Mat m 1 * J := by
    rw [show x2S3Mat m 4 = x2S3Mat m 1 * x2S3Mat m 2 from (x2S3Mat_mul m 1 2).symm,
      Matrix.mul_assoc, show x2S3Mat m 2 = x2S3Swap m from rfl, hS]
  have h2 : x2S3Mat m 2 * J = J := hS
  have hsum : x2S3Avg m * J = (1 / 6 : ℂ) • ((2 : ℂ) • (J + x2S3Mat m 1 * J + x2S3Mat m 5 * J)) := by
    unfold x2S3Avg
    rw [Matrix.smul_mul, Matrix.sum_mul, Fin.sum_univ_six, x2S3Mat_zero, Matrix.one_mul, h2, h3, h4]
    congr 1
    rw [two_smul]
    abel
  rw [h0, smul_smul] at hsum
  have h6 : (1 / 6 * 2 : ℂ) ≠ 0 := by norm_num
  exact (smul_eq_zero.mp hsum.symm).resolve_left h6

theorem x2InvolutionPart_false_fix {n r : Type*} [Fintype n] [DecidableEq n]
    (S : Matrix n n ℂ) (J : Matrix n r ℂ) (hS : S * J = J) :
    x2InvolutionPart S false * J = J := by
  unfold x2InvolutionPart
  rw [Matrix.smul_mul, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, hS]
  simp only [Bool.false_eq_true, ↓reduceIte, one_smul]
  rw [← two_smul ℂ, smul_smul]
  norm_num

theorem x2InvolutionPart_true_fix {n r : Type*} [Fintype n] [DecidableEq n]
    (S : Matrix n n ℂ) (W : Matrix n r ℂ) (hS : S * W = -W) :
    x2InvolutionPart S true * W = W := by
  unfold x2InvolutionPart
  rw [Matrix.smul_mul, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, hS]
  simp only [↓reduceIte, neg_smul, one_smul, neg_neg]
  rw [← two_smul ℂ, smul_smul]
  norm_num

theorem x2S3Std_comm_mat (m : ℕ) (q : Fin 6) :
    x2S3Std m * x2S3Mat m q = x2S3Mat m q * x2S3Std m := by
  rw [x2S3Std, Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul,
    Matrix.mul_one, x2S3Avg_mul_mat, x2S3Mat_mul_avg, x2S3Alt_mul_mat, x2S3Mat_mul_alt]

/-- The partner of an even standard image is odd under the swap. -/
theorem x2_partner_odd (m : ℕ) {r : Type*} [Fintype r] (J : Matrix (Fin (m * (m * m))) r ℂ)
    (hS : x2S3Swap m * J = J) :
    x2S3Swap m * ((x2S3Mat m 1 - x2S3Mat m 5) * J) = -((x2S3Mat m 1 - x2S3Mat m 5) * J) := by
  have h3 : x2S3Mat m 3 * J = x2S3Mat m 5 * J := by
    rw [show x2S3Mat m 3 = x2S3Mat m 5 * x2S3Mat m 2 from (x2S3Mat_mul m 5 2).symm,
      Matrix.mul_assoc]
    exact congrArg _ hS
  have h4 : x2S3Mat m 4 * J = x2S3Mat m 1 * J := by
    rw [show x2S3Mat m 4 = x2S3Mat m 1 * x2S3Mat m 2 from (x2S3Mat_mul m 1 2).symm,
      Matrix.mul_assoc]
    exact congrArg _ hS
  rw [← Matrix.mul_assoc, Matrix.mul_sub, show x2S3Swap m = x2S3Mat m 2 from rfl, x2S3Mat_mul,
    x2S3Mat_mul, show x2Perm3Mul 2 1 = 3 from rfl, show x2Perm3Mul 2 5 = 4 from rfl,
    Matrix.sub_mul (x2S3Mat m 3) (x2S3Mat m 4) J, h3, h4,
    Matrix.sub_mul (x2S3Mat m 1) (x2S3Mat m 5) J, neg_sub]

/-- TRIPLES OF THREE EQUAL TYPES: the h-side form on `(a, a, a)` from the triple's keys. -/
theorem x2_hform_triple (D : X2Data) (wU1 : X2U 1 → Equiv.Perm (Fin 6) → ℂ)
    (wU2 : X2U 2 → Equiv.Perm (Fin 6) → ℂ) (hS : X2SiteFacts D wU1 wU2)
    (hK : X2KeyFrameFacts D) (Nm : X2Blocks 1) (Na : X2Blocks 2)
    (hNm : ∀ k, (x2Complex (Nm k)).PosSemidef) (hNa : ∀ k, (x2Complex (Na k)).PosSemidef)
    (hres : ∀ b, (x2Complex (x2Residual D Nm Na b)).PosSemidef) (a : Fin 7) :
    (x2HForm D Nm Na (a, a, a)).PosSemidef := by
  have hπq := x2_carrier_triple_comm a
  have hfq : ∀ q, (x2TargetQForm (a, a, a) - x2TransferQForm D 1 Nm (a, a, a) -
      x2TransferQForm D 2 Na (a, a, a)) * x2S3Mat (certificatePhysicalFrameSystem0.size a) q =
      x2S3Mat (certificatePhysicalFrameSystem0.size a) q * (x2TargetQForm (a, a, a) -
        x2TransferQForm D 1 Nm (a, a, a) - x2TransferQForm D 2 Na (a, a, a)) := fun q => by
    rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, x2_target_triple_comm,
      x2_transferQForm_triple_comm, x2_transferQForm_triple_comm]
  have hGq := x2_metric_triple_comm a
  have hsym : ∀ k, (Nm k)ᵀ = Nm k := fun k => x2_transpose_eq_of_posSemidef _ (hNm k)
  have hsyma : ∀ k, (Na k)ᵀ = Na k := fun k => x2_transpose_eq_of_posSemidef _ (hNa k)
  -- the facts of a key of kind `k` of the triple, in the S3 forms
  have kf : ∀ (k : ℕ) (b : x2Key 0), x2KeyOf (a, a, a) k = some b →
      certificateCarrierJointAction0 (a, a, a) * x2ImageAt D (a, a, a) b = x2ImageAt D (a, a, a) b ∧
      x2KindProjFrame (a, a, a) k * x2ImageAt D (a, a, a) b = x2ImageAt D (a, a, a) b ∧
      ((x2ImageAt D (a, a, a) b)ᴴ * certificateThreeSiteFrameSystem0.metric (a, a, a) *
        x2ImageAt D (a, a, a) b).det ≠ 0 ∧
      (certificateCarrierJointAction0 (a, a, a) * x2KindProjFrame (a, a, a) k).trace =
        (((if k = 2 then 2 else 1) * x2KeySize 0 b : ℕ) : ℂ) := by
    intro k b h
    obtain ⟨hbτ, hbk⟩ := x2KeyOf_some h
    obtain ⟨h1, h2, h3, h4⟩ := x2_keyFacts_at D hK (a, a, a) b hbτ
    rw [hbk] at h2 h4
    rw [x2_keyDegree_kind b, hbk] at h4
    exact ⟨h1, h2, h3, h4⟩
  have hswap : ∀ b, x2KeyOf (a, a, a) 2 = some b →
      x2S3Swap (certificatePhysicalFrameSystem0.size a) * x2ImageAt D (a, a, a) b =
        x2ImageAt D (a, a, a) b := by
    intro b h
    obtain ⟨hbτ, hbk⟩ := x2KeyOf_some h
    have hdeg : x2KeyDegree 0 b = 2 := by rw [x2_keyDegree_kind b, hbk]; rfl
    have h' := hK.standard_swap b hdeg
    rw [← x2ImageAt_key D b] at h'
    revert h'
    rw [hbτ, x2SlotPermFrame_triple]
    exact id
  have hsplit : ∀ b, x2KeyOf (a, a, a) 2 = some b →
      (certificateCarrierJointAction0 (a, a, a) *
        (x2S3Std (certificatePhysicalFrameSystem0.size a) *
          x2S3Swap (certificatePhysicalFrameSystem0.size a))).trace = 0 := by
    intro b h
    obtain ⟨hbτ, hbk⟩ := x2KeyOf_some h
    have hdeg : x2KeyDegree 0 b = 2 := by rw [x2_keyDegree_kind b, hbk]; rfl
    have h' := hK.standard_split b hdeg
    revert h'
    rw [hbτ, x2SlotPermFrame_triple, x2KindProjFrame_triple, Matrix.mul_assoc]
    simp only [show (2 : ℕ) ≠ 0 by decide, show (2 : ℕ) ≠ 1 by decide, if_false]
    exact id
  have hempty : ∀ k : ℕ, k < 3 → x2KeyOf (a, a, a) k = none →
      (certificateCarrierJointAction0 (a, a, a) * x2KindProjFrame (a, a, a) k).trace = 0 :=
    fun k hk ho => hK.empty_kinds (a, a, a) le_rfl le_rfl k (by simpa [x2NumKinds] using hk)
      (x2KeyOf_none ho)
  have hstd_eq : x2KindProjFrame (a, a, a) 2 = x2S3Std (certificatePhysicalFrameSystem0.size a) := by
    rw [x2KindProjFrame_triple]; rfl
  have hπstd_idem : (certificateCarrierJointAction0 (a, a, a) *
      x2S3Std (certificatePhysicalFrameSystem0.size a)) *
      (certificateCarrierJointAction0 (a, a, a) * x2S3Std (certificatePhysicalFrameSystem0.size a)) =
      certificateCarrierJointAction0 (a, a, a) * x2S3Std (certificatePhysicalFrameSystem0.size a) := by
    have hc : certificateCarrierJointAction0 (a, a, a) * x2S3Std (certificatePhysicalFrameSystem0.size a) =
        x2S3Std (certificatePhysicalFrameSystem0.size a) * certificateCarrierJointAction0 (a, a, a) := by
      have h0 := x2S3Part_comm _ _ hπq 0
      have h1 := x2S3Part_comm _ _ hπq 1
      change certificateCarrierJointAction0 (a, a, a) * x2S3Avg _ =
        x2S3Avg _ * certificateCarrierJointAction0 (a, a, a) at h0
      change certificateCarrierJointAction0 (a, a, a) * x2S3Alt _ =
        x2S3Alt _ * certificateCarrierJointAction0 (a, a, a) at h1
      rw [x2S3Std, Matrix.mul_sub, Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_one,
        Matrix.one_mul, h0, h1]
    calc _ = certificateCarrierJointAction0 (a, a, a) *
          (x2S3Std (certificatePhysicalFrameSystem0.size a) * certificateCarrierJointAction0 (a, a, a)) *
          x2S3Std (certificatePhysicalFrameSystem0.size a) := by simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [← hc]
        simp only [← Matrix.mul_assoc]
        rw [certificateCarrierJointAction0_idempotent, Matrix.mul_assoc, x2S3Std_idem]
  refine x2_posSemidef_of_parts_complex (certificateCarrierJointAction0 (a, a, a))
    (x2TargetQForm (a, a, a) - x2TransferQForm D 1 Nm (a, a, a) - x2TransferQForm D 2 Na (a, a, a))
    (certificateThreeSiteFrameSystem0.metric (a, a, a))
    (x2S3Part (certificatePhysicalFrameSystem0.size a)) (x2S3Part_sum _)
    (certificateCarrierJointAction0_idempotent _) (fun k => x2S3Part_comm _ _ hπq k)
    (x2S3Part_mul _) (x2S3Part_conjTranspose _) (fun k => x2S3Part_comm _ _ hfq k)
    (x2TripleM D a) ?_ ?_ ?_ ?_
  · -- the carrier part fixes the spanning matrix
    intro k
    match k with
    | 0 =>
        show certificateCarrierJointAction0 (a, a, a) * x2S3Avg (certificatePhysicalFrameSystem0.size a) *
          x2PartImage D (a, a, a) (x2KeyOf (a, a, a) 0) = x2PartImage D (a, a, a) (x2KeyOf (a, a, a) 0)
        have key : ∀ o : Option (x2Key 0), x2KeyOf (a, a, a) 0 = o →
            certificateCarrierJointAction0 (a, a, a) * x2S3Avg (certificatePhysicalFrameSystem0.size a) *
              x2PartImage D (a, a, a) o = x2PartImage D (a, a, a) o := by
          intro o ho
          cases o with
          | none => simp only [x2PartImage, Matrix.mul_zero]
          | some b =>
              obtain ⟨h1, h2, -, -⟩ := kf 0 b ho
              rw [x2KindProjFrame_triple] at h2
              simp only [↓reduceIte] at h2
              show certificateCarrierJointAction0 (a, a, a) * x2S3Avg (certificatePhysicalFrameSystem0.size a) *
                x2ImageAt D (a, a, a) b = x2ImageAt D (a, a, a) b
              rw [Matrix.mul_assoc, h2, h1]
        exact key _ rfl
    | 1 =>
        show certificateCarrierJointAction0 (a, a, a) * x2S3Alt (certificatePhysicalFrameSystem0.size a) *
          x2PartImage D (a, a, a) (x2KeyOf (a, a, a) 1) = x2PartImage D (a, a, a) (x2KeyOf (a, a, a) 1)
        have key : ∀ o : Option (x2Key 0), x2KeyOf (a, a, a) 1 = o →
            certificateCarrierJointAction0 (a, a, a) * x2S3Alt (certificatePhysicalFrameSystem0.size a) *
              x2PartImage D (a, a, a) o = x2PartImage D (a, a, a) o := by
          intro o ho
          cases o with
          | none => simp only [x2PartImage, Matrix.mul_zero]
          | some b =>
              obtain ⟨h1, h2, -, -⟩ := kf 1 b ho
              rw [x2KindProjFrame_triple] at h2
              simp only [one_ne_zero, ↓reduceIte] at h2
              show certificateCarrierJointAction0 (a, a, a) * x2S3Alt (certificatePhysicalFrameSystem0.size a) *
                x2ImageAt D (a, a, a) b = x2ImageAt D (a, a, a) b
              rw [Matrix.mul_assoc, h2, h1]
        exact key _ rfl
    | 2 =>
        show certificateCarrierJointAction0 (a, a, a) *
          (x2S3Std (certificatePhysicalFrameSystem0.size a) * x2InvolutionPart (x2S3Swap (certificatePhysicalFrameSystem0.size a)) false) *
          x2PartImage D (a, a, a) (x2KeyOf (a, a, a) 2) = x2PartImage D (a, a, a) (x2KeyOf (a, a, a) 2)
        have key : ∀ o : Option (x2Key 0), x2KeyOf (a, a, a) 2 = o →
            certificateCarrierJointAction0 (a, a, a) *
              (x2S3Std (certificatePhysicalFrameSystem0.size a) * x2InvolutionPart (x2S3Swap (certificatePhysicalFrameSystem0.size a)) false) *
              x2PartImage D (a, a, a) o = x2PartImage D (a, a, a) o := by
          intro o ho
          cases o with
          | none => simp only [x2PartImage, Matrix.mul_zero]
          | some b =>
              obtain ⟨h1, h2, -, -⟩ := kf 2 b ho
              rw [hstd_eq] at h2
              show certificateCarrierJointAction0 (a, a, a) *
                (x2S3Std (certificatePhysicalFrameSystem0.size a) * x2InvolutionPart (x2S3Swap (certificatePhysicalFrameSystem0.size a)) false) *
                x2ImageAt D (a, a, a) b = x2ImageAt D (a, a, a) b
              rw [Matrix.mul_assoc, Matrix.mul_assoc,
                x2InvolutionPart_false_fix _ _ (hswap b ho), h2, h1]
        exact key _ rfl
    | 3 =>
        show certificateCarrierJointAction0 (a, a, a) *
          (x2S3Std (certificatePhysicalFrameSystem0.size a) * x2InvolutionPart (x2S3Swap (certificatePhysicalFrameSystem0.size a)) true) *
          x2PartPartner D a (x2KeyOf (a, a, a) 2) = x2PartPartner D a (x2KeyOf (a, a, a) 2)
        have key : ∀ o : Option (x2Key 0), x2KeyOf (a, a, a) 2 = o →
            certificateCarrierJointAction0 (a, a, a) *
              (x2S3Std (certificatePhysicalFrameSystem0.size a) * x2InvolutionPart (x2S3Swap (certificatePhysicalFrameSystem0.size a)) true) *
              x2PartPartner D a o = x2PartPartner D a o := by
          intro o ho
          cases o with
          | none => simp only [x2PartPartner, Matrix.mul_zero]
          | some b =>
              obtain ⟨h1, h2, -, -⟩ := kf 2 b ho
              rw [hstd_eq] at h2
              show certificateCarrierJointAction0 (a, a, a) *
                (x2S3Std (certificatePhysicalFrameSystem0.size a) * x2InvolutionPart (x2S3Swap (certificatePhysicalFrameSystem0.size a)) true) *
                ((x2S3Mat (certificatePhysicalFrameSystem0.size a) 1 - x2S3Mat (certificatePhysicalFrameSystem0.size a) 5) * x2ImageAt D (a, a, a) b) =
                (x2S3Mat (certificatePhysicalFrameSystem0.size a) 1 - x2S3Mat (certificatePhysicalFrameSystem0.size a) 5) * x2ImageAt D (a, a, a) b
              have hW := x2_partner_odd _ (x2ImageAt D (a, a, a) b) (hswap b ho)
              have hstdW : x2S3Std (certificatePhysicalFrameSystem0.size a) *
                  ((x2S3Mat (certificatePhysicalFrameSystem0.size a) 1 - x2S3Mat (certificatePhysicalFrameSystem0.size a) 5) * x2ImageAt D (a, a, a) b) =
                  (x2S3Mat (certificatePhysicalFrameSystem0.size a) 1 - x2S3Mat (certificatePhysicalFrameSystem0.size a) 5) * x2ImageAt D (a, a, a) b := by
                rw [← Matrix.mul_assoc, Matrix.mul_sub, x2S3Std_comm_mat, x2S3Std_comm_mat,
                  ← Matrix.sub_mul, Matrix.mul_assoc, h2]
              have hπW : certificateCarrierJointAction0 (a, a, a) *
                  ((x2S3Mat (certificatePhysicalFrameSystem0.size a) 1 - x2S3Mat (certificatePhysicalFrameSystem0.size a) 5) * x2ImageAt D (a, a, a) b) =
                  (x2S3Mat (certificatePhysicalFrameSystem0.size a) 1 - x2S3Mat (certificatePhysicalFrameSystem0.size a) 5) * x2ImageAt D (a, a, a) b := by
                rw [← Matrix.mul_assoc, Matrix.mul_sub, hπq, hπq, ← Matrix.sub_mul, Matrix.mul_assoc,
                  h1]
              rw [Matrix.mul_assoc, Matrix.mul_assoc, x2InvolutionPart_true_fix _ _ hW, hstdW, hπW]
        exact key _ rfl
  · -- nondegenerate metrics
    intro k
    match k with
    | 0 =>
        show ((x2PartImage D (a, a, a) (x2KeyOf (a, a, a) 0))ᴴ *
          certificateThreeSiteFrameSystem0.metric (a, a, a) *
            x2PartImage D (a, a, a) (x2KeyOf (a, a, a) 0)).det ≠ 0
        generalize ho : x2KeyOf (a, a, a) 0 = o
        cases o with
        | none => rw [Matrix.det_isEmpty]; exact one_ne_zero
        | some b => exact (kf 0 b ho).2.2.1
    | 1 =>
        show ((x2PartImage D (a, a, a) (x2KeyOf (a, a, a) 1))ᴴ *
          certificateThreeSiteFrameSystem0.metric (a, a, a) *
            x2PartImage D (a, a, a) (x2KeyOf (a, a, a) 1)).det ≠ 0
        generalize ho : x2KeyOf (a, a, a) 1 = o
        cases o with
        | none => rw [Matrix.det_isEmpty]; exact one_ne_zero
        | some b => exact (kf 1 b ho).2.2.1
    | 2 =>
        show ((x2PartImage D (a, a, a) (x2KeyOf (a, a, a) 2))ᴴ *
          certificateThreeSiteFrameSystem0.metric (a, a, a) *
            x2PartImage D (a, a, a) (x2KeyOf (a, a, a) 2)).det ≠ 0
        generalize ho : x2KeyOf (a, a, a) 2 = o
        cases o with
        | none => rw [Matrix.det_isEmpty]; exact one_ne_zero
        | some b => exact (kf 2 b ho).2.2.1
    | 3 =>
        show ((x2PartPartner D a (x2KeyOf (a, a, a) 2))ᴴ *
          certificateThreeSiteFrameSystem0.metric (a, a, a) *
            x2PartPartner D a (x2KeyOf (a, a, a) 2)).det ≠ 0
        generalize ho : x2KeyOf (a, a, a) 2 = o
        cases o with
        | none => rw [Matrix.det_isEmpty]; exact one_ne_zero
        | some b =>
            obtain ⟨h1, h2, h3, -⟩ := kf 2 b ho
            rw [hstd_eq] at h2
            show ((x2PartnerAt D a b)ᴴ * certificateThreeSiteFrameSystem0.metric (a, a, a) *
              x2PartnerAt D a b).det ≠ 0
            unfold x2PartnerAt
            have hJ := x2_standard_relation _ (x2ImageAt D (a, a, a) b) h2 (hswap b ho)
            rw [x2_partner_form _ _ _ _ (by rw [x2S3Mat_mul]; exact x2S3Mat_zero _)
              (by rw [x2S3Mat_mul]; exact x2S3Mat_zero _)
              (by rw [x2S3Mat_conjTranspose]; rfl) (by rw [x2S3Mat_conjTranspose]; rfl)
              (hGq 1) (hGq 5) hJ, Matrix.det_smul]
            exact mul_ne_zero (pow_ne_zero _ (by norm_num)) h3
  · -- traces
    intro k
    match k with
    | 0 =>
        show (certificateCarrierJointAction0 (a, a, a) * x2S3Avg _).trace =
          (Fintype.card (x2PartCols (x2KeyOf (a, a, a) 0)) : ℂ)
        rw [x2PartCols_card]
        generalize ho : x2KeyOf (a, a, a) 0 = o
        cases o with
        | none =>
            have h := hempty 0 (by decide) ho
            rw [x2KindProjFrame_triple] at h
            simp only [↓reduceIte] at h
            rw [h]; simp [x2PartSize]
        | some b =>
            have h := (kf 0 b ho).2.2.2
            rw [x2KindProjFrame_triple] at h
            simp only [↓reduceIte, show (0 : ℕ) ≠ 2 by decide, one_mul] at h
            rw [h]; rfl
    | 1 =>
        show (certificateCarrierJointAction0 (a, a, a) * x2S3Alt _).trace =
          (Fintype.card (x2PartCols (x2KeyOf (a, a, a) 1)) : ℂ)
        rw [x2PartCols_card]
        generalize ho : x2KeyOf (a, a, a) 1 = o
        cases o with
        | none =>
            have h := hempty 1 (by decide) ho
            rw [x2KindProjFrame_triple] at h
            simp only [one_ne_zero, ↓reduceIte] at h
            rw [h]; simp [x2PartSize]
        | some b =>
            have h := (kf 1 b ho).2.2.2
            rw [x2KindProjFrame_triple] at h
            simp only [one_ne_zero, ↓reduceIte, show (1 : ℕ) ≠ 2 by decide, one_mul] at h
            rw [h]; rfl
    | 2 =>
        show (certificateCarrierJointAction0 (a, a, a) *
          (x2S3Std _ * x2InvolutionPart (x2S3Swap _) false)).trace =
          (Fintype.card (x2PartCols (x2KeyOf (a, a, a) 2)) : ℂ)
        rw [x2PartCols_card, x2_trace_stdHalf]
        generalize ho : x2KeyOf (a, a, a) 2 = o
        cases o with
        | none =>
            have h := hempty 2 (by decide) ho
            rw [hstd_eq] at h
            have h0 := x2_eq_zero_of_idempotent_trace_zero_complex _ hπstd_idem h
            rw [← Matrix.mul_assoc, h0, Matrix.zero_mul, Matrix.trace_zero]
            simp [x2PartSize]
        | some b =>
            have h := (kf 2 b ho).2.2.2
            rw [hstd_eq] at h
            rw [h, hsplit b ho]
            simp only [x2PartSize, ↓reduceIte, mul_zero, add_zero, Bool.false_eq_true]
            push_cast
            ring
    | 3 =>
        show (certificateCarrierJointAction0 (a, a, a) *
          (x2S3Std _ * x2InvolutionPart (x2S3Swap _) true)).trace =
          (Fintype.card (x2PartCols (x2KeyOf (a, a, a) 2)) : ℂ)
        rw [x2PartCols_card, x2_trace_stdHalf]
        generalize ho : x2KeyOf (a, a, a) 2 = o
        cases o with
        | none =>
            have h := hempty 2 (by decide) ho
            rw [hstd_eq] at h
            have h0 := x2_eq_zero_of_idempotent_trace_zero_complex _ hπstd_idem h
            rw [← Matrix.mul_assoc, h0, Matrix.zero_mul, Matrix.trace_zero]
            simp [x2PartSize]
        | some b =>
            have h := (kf 2 b ho).2.2.2
            rw [hstd_eq] at h
            rw [h, hsplit b ho]
            simp only [x2PartSize, ↓reduceIte, mul_zero, add_zero, Bool.false_eq_true]
            push_cast
            ring
  · -- positive reduced blocks
    intro k
    match k with
    | 0 =>
        show ((x2PartImage D (a, a, a) (x2KeyOf (a, a, a) 0))ᴴ * _ *
          x2PartImage D (a, a, a) (x2KeyOf (a, a, a) 0)).PosSemidef
        generalize ho : x2KeyOf (a, a, a) 0 = o
        cases o with
        | none =>
            have : ((x2PartImage D (a, a, a) none)ᴴ * (x2TargetQForm (a, a, a) -
                x2TransferQForm D 1 Nm (a, a, a) - x2TransferQForm D 2 Na (a, a, a)) *
                x2PartImage D (a, a, a) none) = 0 := by ext i j; exact isEmptyElim i
            rw [this]; exact Matrix.PosSemidef.zero
        | some b =>
            show ((x2ImageAt D (a, a, a) b)ᴴ * _ * x2ImageAt D (a, a, a) b).PosSemidef
            rw [x2_hblock_identity_at D hS.target Nm Na hsym hsyma (a, a, a) b (x2KeyOf_some ho).1]
            exact hres b
    | 1 =>
        show ((x2PartImage D (a, a, a) (x2KeyOf (a, a, a) 1))ᴴ * _ *
          x2PartImage D (a, a, a) (x2KeyOf (a, a, a) 1)).PosSemidef
        generalize ho : x2KeyOf (a, a, a) 1 = o
        cases o with
        | none =>
            have : ((x2PartImage D (a, a, a) none)ᴴ * (x2TargetQForm (a, a, a) -
                x2TransferQForm D 1 Nm (a, a, a) - x2TransferQForm D 2 Na (a, a, a)) *
                x2PartImage D (a, a, a) none) = 0 := by ext i j; exact isEmptyElim i
            rw [this]; exact Matrix.PosSemidef.zero
        | some b =>
            show ((x2ImageAt D (a, a, a) b)ᴴ * _ * x2ImageAt D (a, a, a) b).PosSemidef
            rw [x2_hblock_identity_at D hS.target Nm Na hsym hsyma (a, a, a) b (x2KeyOf_some ho).1]
            exact hres b
    | 2 =>
        show ((x2PartImage D (a, a, a) (x2KeyOf (a, a, a) 2))ᴴ * _ *
          x2PartImage D (a, a, a) (x2KeyOf (a, a, a) 2)).PosSemidef
        generalize ho : x2KeyOf (a, a, a) 2 = o
        cases o with
        | none =>
            have : ((x2PartImage D (a, a, a) none)ᴴ * (x2TargetQForm (a, a, a) -
                x2TransferQForm D 1 Nm (a, a, a) - x2TransferQForm D 2 Na (a, a, a)) *
                x2PartImage D (a, a, a) none) = 0 := by ext i j; exact isEmptyElim i
            rw [this]; exact Matrix.PosSemidef.zero
        | some b =>
            show ((x2ImageAt D (a, a, a) b)ᴴ * _ * x2ImageAt D (a, a, a) b).PosSemidef
            rw [x2_hblock_identity_at D hS.target Nm Na hsym hsyma (a, a, a) b (x2KeyOf_some ho).1]
            exact hres b
    | 3 =>
        show ((x2PartPartner D a (x2KeyOf (a, a, a) 2))ᴴ * _ *
          x2PartPartner D a (x2KeyOf (a, a, a) 2)).PosSemidef
        generalize ho : x2KeyOf (a, a, a) 2 = o
        cases o with
        | none =>
            have : ((x2PartPartner D a none)ᴴ * (x2TargetQForm (a, a, a) -
                x2TransferQForm D 1 Nm (a, a, a) - x2TransferQForm D 2 Na (a, a, a)) *
                x2PartPartner D a none) = 0 := by ext i j; exact isEmptyElim i
            rw [this]; exact Matrix.PosSemidef.zero
        | some b =>
            obtain ⟨-, h2, -, -⟩ := kf 2 b ho
            rw [hstd_eq] at h2
            show ((x2PartnerAt D a b)ᴴ * _ * x2PartnerAt D a b).PosSemidef
            unfold x2PartnerAt
            have hJ := x2_standard_relation _ (x2ImageAt D (a, a, a) b) h2 (hswap b ho)
            rw [x2_partner_form _ _ _ _ (by rw [x2S3Mat_mul]; exact x2S3Mat_zero _)
              (by rw [x2S3Mat_mul]; exact x2S3Mat_zero _)
              (by rw [x2S3Mat_conjTranspose]; rfl) (by rw [x2S3Mat_conjTranspose]; rfl)
              (hfq 1) (hfq 5) hJ,
              x2_hblock_identity_at D hS.target Nm Na hsym hsyma (a, a, a) b (x2KeyOf_some ho).1]
            exact (hres b).smul (by simpa using x2_ratCast_nonneg (show (0 : ℚ) ≤ 3 by norm_num))

/-- The bridge: T2.1a from the per-site facts, the per-key facts, positive source
blocks and positive reduced residual blocks. -/
theorem x2_qutritEndpointInequality_of_facts' (D : X2Data)
    (wU1 : X2U 1 → Equiv.Perm (Fin 6) → ℂ) (wU2 : X2U 2 → Equiv.Perm (Fin 6) → ℂ)
    (hS : X2SiteFacts D wU1 wU2) (hK : X2KeyFrameFacts D) (Nm : X2Blocks 1) (Na : X2Blocks 2)
    (hNm : ∀ k, (x2Complex (Nm k)).PosSemidef) (hNa : ∀ k, (x2Complex (Na k)).PosSemidef)
    (hres : ∀ b, (x2Complex (x2Residual D Nm Na b)).PosSemidef) :
    QutritEndpointInequality :=
  x2_qutritEndpointInequality_of_facts D wU1 wU2 hS hK Nm Na hNm hNa hres
    (x2_hform_triple D wU1 wU2 hS hK Nm Na hNm hNa hres)

/-- The reduced bridge statement of CertificateX2Reduced (`X2ReducedBridge D`, the route-X2 form
of `hbridge`) from the per-site facts and the per-key facts. -/
theorem x2_reducedBridge_of_facts (D : X2Data)
    (wU1 : X2U 1 → Equiv.Perm (Fin 6) → ℂ) (wU2 : X2U 2 → Equiv.Perm (Fin 6) → ℂ)
    (hS : X2SiteFacts D wU1 wU2) (hK : X2KeyFrameFacts D) : X2ReducedBridge D :=
  fun Nm Na hNm hNa hres => x2_qutritEndpointInequality_of_facts' D wU1 wU2 hS hK Nm Na hNm hNa hres

end ThreeCopyQutritWerner

end
