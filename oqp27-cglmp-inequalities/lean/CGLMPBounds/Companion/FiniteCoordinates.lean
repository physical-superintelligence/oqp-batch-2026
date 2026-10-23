module

public import CGLMPBounds.Companion.PhysicalPVM
public import CGLMPBounds.Companion.FiniteDefinitions

@[expose] public section


/-!
# Identifying the companion multiplicity with `Fin (4*n)`

This is an explicit change of finite matrix coordinates. The target definitions
are the source-only definitions of `Companion/FiniteDefinitions.lean`.
The original strategy and its trace normalization are not changed.
-/

open Matrix
open scoped Kronecker
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid
namespace CGLMPBounds.Companion
noncomputable section

variable {d n : ℕ} [NeZero d]

def multiplicityEquiv : CompanionMultiplicity n ≃ Fin (4 * n) := finProdFinEquiv

def physicalEquiv : CompanionSpace d n ≃ CompanionFinite.Physical d n :=
  Equiv.prodCongr (Equiv.refl (ZMod d)) multiplicityEquiv

def frequencyEquiv : (Fin d × CompanionMultiplicity n) ≃ (Fin d × Fin (4 * n)) :=
  Equiv.prodCongr (Equiv.refl (Fin d)) multiplicityEquiv

def multiplicityReindex :
    Matrix (CompanionMultiplicity n) (CompanionMultiplicity n) ℂ ≃+*
      CompanionFinite.MultiplicityMat n :=
  Matrix.reindexRingEquiv ℂ multiplicityEquiv

def physicalReindex : CompanionMat d n ≃+* CompanionFinite.PhysicalMat d n :=
  Matrix.reindexRingEquiv ℂ physicalEquiv

def frequencyReindex :
    Matrix (Fin d × CompanionMultiplicity n) (Fin d × CompanionMultiplicity n) ℂ ≃+*
      Matrix (Fin d × Fin (4 * n)) (Fin d × Fin (4 * n)) ℂ :=
  Matrix.reindexRingEquiv ℂ frequencyEquiv

lemma multiplicityReindex_star
    (X : Matrix (CompanionMultiplicity n) (CompanionMultiplicity n) ℂ) :
    multiplicityReindex Xᴴ = (multiplicityReindex X)ᴴ := rfl

lemma physicalReindex_star (X : CompanionMat d n) :
    physicalReindex Xᴴ = (physicalReindex X)ᴴ := rfl

lemma multiplicityReindex_trace
    (X : Matrix (CompanionMultiplicity n) (CompanionMultiplicity n) ℂ) :
    Matrix.trace (multiplicityReindex X) = Matrix.trace X := by
  exact Fintype.sum_equiv (multiplicityEquiv (n := n)).symm _ _ (fun _ => rfl)

def finiteUnitary (U : Matrix.unitaryGroup (CompanionMultiplicity n) ℂ) :
    Matrix.unitaryGroup (Fin (4 * n)) ℂ :=
  ⟨multiplicityReindex (U : Matrix (CompanionMultiplicity n) (CompanionMultiplicity n) ℂ),
    by
      rw [Matrix.star_eq_conjTranspose, ← multiplicityReindex_star, ← map_mul,
        ← Matrix.star_eq_conjTranspose, U.property.1, map_one]
    , by
      rw [Matrix.star_eq_conjTranspose, ← multiplicityReindex_star, ← map_mul,
        ← Matrix.star_eq_conjTranspose, U.property.2, map_one]⟩

def finiteTuple (V : Fin d → Matrix.unitaryGroup (CompanionMultiplicity n) ℂ) :
    CompanionFinite.Tuple d n := fun j => finiteUnitary (V j)

lemma finiteTuple_coe (V : Fin d → Matrix.unitaryGroup (CompanionMultiplicity n) ℂ)
    (j : Fin d) :
    (finiteTuple V j : CompanionFinite.MultiplicityMat n) =
      multiplicityReindex (V j : Matrix (CompanionMultiplicity n) (CompanionMultiplicity n) ℂ) := rfl

lemma finiteTuple_fourth (V : Fin d → Matrix.unitaryGroup (CompanionMultiplicity n) ℂ)
    (hfour : ∀ j, (V j : Matrix (CompanionMultiplicity n) (CompanionMultiplicity n) ℂ) ^ 4 = 1)
    (j : Fin d) : (finiteTuple V j : CompanionFinite.MultiplicityMat n) ^ 4 = 1 := by
  rw [finiteTuple_coe, ← map_pow, hfour j, map_one]

lemma sourcePhase_eq_finite (j : Fin d) : sourcePhase j = CompanionFinite.phase j := by
  rw [sourcePhase_apply, CompanionFinite.phase]
  congr 1
  push_cast
  ring

lemma liftedFourier_finite :
    (liftedFourier (d := d) (ι := CompanionMultiplicity n)).submatrix
        physicalEquiv.symm frequencyEquiv.symm = CompanionFinite.fourierLift d n := by
  ext p q
  change outcomeFourier p.1 q.1 *
      (1 : Matrix (CompanionMultiplicity n) (CompanionMultiplicity n) ℂ)
        (multiplicityEquiv.symm p.2) (multiplicityEquiv.symm q.2) =
    CompanionFinite.fourierMatrix d p.1 q.1 *
      (1 : CompanionFinite.MultiplicityMat n) p.2 q.2
  rw [outcomeFourier_apply]
  simp only [CompanionFinite.fourierMatrix, Matrix.one_apply,
    multiplicityEquiv.symm.injective.eq_iff]

lemma frequencyDiagonal_finite
    (V : Fin d → Matrix.unitaryGroup (CompanionMultiplicity n) ℂ) :
    frequencyReindex (frequencyDiagonal (fun j => sourcePhase j •
      (V j : Matrix (CompanionMultiplicity n) (CompanionMultiplicity n) ℂ))) =
        CompanionFinite.frequencyOperator (finiteTuple V) := by
  ext p q
  rcases p with ⟨j, u⟩
  rcases q with ⟨k, v⟩
  change (if j = k then sourcePhase j •
      (V j : Matrix (CompanionMultiplicity n) (CompanionMultiplicity n) ℂ) else 0)
      (multiplicityEquiv.symm u) (multiplicityEquiv.symm v) =
    (if j = k then CompanionFinite.phase j •
      (finiteTuple V j : CompanionFinite.MultiplicityMat n) else 0) u v
  by_cases h : j = k
  · simp only [h, if_pos, Matrix.smul_apply, smul_eq_mul, sourcePhase_eq_finite]
    rfl
  · simp only [h, if_false, Matrix.zero_apply]

lemma tupleClock_finite (V : Fin d → Matrix.unitaryGroup (CompanionMultiplicity n) ℂ) :
    physicalReindex (tupleClock V) = CompanionFinite.clock (finiteTuple V) := by
  let F := liftedFourier (d := d) (ι := CompanionMultiplicity n)
  let D := frequencyDiagonal (fun j => sourcePhase j •
    (V j : Matrix (CompanionMultiplicity n) (CompanionMultiplicity n) ℂ))
  change (F * D * Fᴴ).submatrix physicalEquiv.symm physicalEquiv.symm = _
  have hF : F.submatrix physicalEquiv.symm frequencyEquiv.symm =
      CompanionFinite.fourierLift d n := liftedFourier_finite
  have hD : D.submatrix frequencyEquiv.symm frequencyEquiv.symm =
      CompanionFinite.frequencyOperator (finiteTuple V) := frequencyDiagonal_finite V
  have hFH : Fᴴ.submatrix frequencyEquiv.symm physicalEquiv.symm =
      (CompanionFinite.fourierLift d n)ᴴ := by
    rw [← Matrix.conjTranspose_submatrix, hF]
  calc
    _ = F.submatrix physicalEquiv.symm frequencyEquiv.symm *
        D.submatrix frequencyEquiv.symm frequencyEquiv.symm *
        Fᴴ.submatrix frequencyEquiv.symm physicalEquiv.symm := by
      rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
    _ = _ := by rw [hF, hD, hFH]; rfl

lemma sourceComputational_finite (a : ZMod d) :
    physicalReindex (sourceComputational (n := n) a) = CompanionFinite.computational a := by
  ext p q
  change (if physicalEquiv.symm p = physicalEquiv.symm q then
      (if p.1 = a then (1 : ℂ) else 0) else 0) =
    (if p = q then (if p.1 = a then (1 : ℂ) else 0) else 0)
  simp only [physicalEquiv.symm.injective.eq_iff]

lemma tupleMeasurement_finite
    (V : Fin d → Matrix.unitaryGroup (CompanionMultiplicity n) ℂ) (t : Fin 4) (a : ZMod d) :
    physicalReindex (tupleMeasurement V t a) = CompanionFinite.measurement (finiteTuple V) t a := by
  simp only [tupleMeasurement, CompanionFinite.measurement, map_mul, map_pow,
    physicalReindex_star, tupleClock_finite, sourceComputational_finite]

lemma correlation_finite (V : Fin d → Matrix.unitaryGroup (CompanionMultiplicity n) ℂ)
    (j k : Fin d) :
    CompanionFinite.correlation (finiteTuple V) j k = unitaryCorrelation V j k := by
  unfold CompanionFinite.correlation unitaryCorrelation
  rw [finiteTuple_coe, finiteTuple_coe, ← multiplicityReindex_star, ← map_mul,
    multiplicityReindex_trace, card_companionMultiplicity]

lemma gap_finite (V : Fin d → Matrix.unitaryGroup (CompanionMultiplicity n) ℂ) :
    CompanionFinite.gap (finiteTuple V) = companionGap V := by
  simp only [CompanionFinite.gap, companionGap, gapPair, correlation_finite]

/-- Reindex a common embedding, keeping its original `Fin n` domain fixed. -/
def finiteEmbedding (Z : Matrix (CompanionSpace d n) (Fin n) ℂ) :
    Matrix (CompanionFinite.Physical d n) (Fin n) ℂ :=
  Z.submatrix physicalEquiv.symm id

lemma finiteEmbedding_star_mul (Z : Matrix (CompanionSpace d n) (Fin n) ℂ)
    (hZ : Zᴴ * Z = 1) : (finiteEmbedding Z)ᴴ * finiteEmbedding Z = 1 := by
  simp only [finiteEmbedding, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
    hZ, Matrix.submatrix_id_id]

lemma finiteEmbedding_range (Z : Matrix (CompanionSpace d n) (Fin n) ℂ) :
    finiteEmbedding Z * (finiteEmbedding Z)ᴴ = physicalReindex (Z * Zᴴ) := by
  change Z.submatrix physicalEquiv.symm (Equiv.refl (Fin n)) *
      Zᴴ.submatrix (Equiv.refl (Fin n)) physicalEquiv.symm =
    (Z * Zᴴ).submatrix physicalEquiv.symm physicalEquiv.symm
  exact Matrix.submatrix_mul_equiv _ _ _ _ _

lemma finiteEmbedding_intertwines (X : CompanionMat d n) (Y : Base n)
    (Z : Matrix (CompanionSpace d n) (Fin n) ℂ) (h : X * Z = Z * Y) :
    physicalReindex X * finiteEmbedding Z = finiteEmbedding Z * Y := by
  change X.submatrix physicalEquiv.symm physicalEquiv.symm *
      Z.submatrix physicalEquiv.symm id = Z.submatrix physicalEquiv.symm id * Y
  rw [Matrix.submatrix_mul_equiv, h]
  exact (Matrix.submatrix_mul_equiv Z Y physicalEquiv.symm (Equiv.refl (Fin n)) id).symm

/-- Full C.1 in the exact finite-coordinate source definitions. -/
theorem exists_companion_finite (hd : 2 ≤ d) (hn : 1 ≤ n)
    (P : Fin 4 → ZMod d → Base n) (hP : ∀ t, IsPVM (P t)) :
    ∃ V : CompanionFinite.Tuple d n,
      (∀ j, (V j : CompanionFinite.MultiplicityMat n) ^ 4 = 1) ∧
      cglmpFourierValue d - cglmp d (tracialTable ![P 0, P 2] ![P 1, P 3]) =
        (8 * (d : ℝ) / ((d : ℝ) - 1)) * CompanionFinite.gap V ∧
      (∀ t a, (CompanionFinite.measurement V t a).IsHermitian ∧
        CompanionFinite.measurement V t a * CompanionFinite.measurement V t a =
          CompanionFinite.measurement V t a) ∧
      (∀ t, ∑ a, CompanionFinite.measurement V t a = 1) ∧
      ∃ Z : Matrix (CompanionFinite.Physical d n) (Fin n) ℂ,
        Zᴴ * Z = 1 ∧
        (∀ t a, CompanionFinite.measurement V t a * Z = Z * P t a) ∧
        (∀ t a, Commute (CompanionFinite.measurement V t a) (Z * Zᴴ)) := by
  obtain ⟨V, hfour, hgap, hpvm, hsum, Z, hiso, hinter, hcomm⟩ :=
    exists_companion_full_product hd hn P hP
  refine ⟨finiteTuple V, finiteTuple_fourth V hfour, ?_, ?_, ?_, finiteEmbedding Z,
    finiteEmbedding_star_mul Z hiso, ?_, ?_⟩
  · rw [gap_finite]
    exact hgap
  · intro t a
    rw [← tupleMeasurement_finite]
    constructor
    · change (physicalReindex (tupleMeasurement V t a))ᴴ = physicalReindex (tupleMeasurement V t a)
      rw [← physicalReindex_star, (hpvm t a).1.eq]
    · rw [← map_mul, (hpvm t a).2]
  · intro t
    simp only [← tupleMeasurement_finite, ← map_sum, hsum t, map_one]
  · intro t a
    rw [← tupleMeasurement_finite]
    exact finiteEmbedding_intertwines _ _ Z (hinter t a)
  · intro t a
    rw [← tupleMeasurement_finite, finiteEmbedding_range]
    change physicalReindex (tupleMeasurement V t a) * physicalReindex (Z * Zᴴ) =
      physicalReindex (Z * Zᴴ) * physicalReindex (tupleMeasurement V t a)
    rw [← map_mul, ← map_mul, (hcomm t a).eq]

end
end CGLMPBounds.Companion
