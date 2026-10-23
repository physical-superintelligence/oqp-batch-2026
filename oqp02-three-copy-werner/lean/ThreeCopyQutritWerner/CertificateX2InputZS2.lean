module

public import ThreeCopyQutritWerner.CertificateX2InputLab

@[expose] public section


/-! The sorted type triples of sector 2 whose keys contribute no part (or with a type of multiplicity 0): x2EmbedS vanishes on their labels. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InZS2
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

noncomputable def ks000 : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := []
theorem z000 (N : X2Blocks 2) (hN : ∀ k, (N k)ᵀ = N k)  : ZspecS 2 N 0 0 0 := by
  have hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![0, 0, 0] ↔ k ∈ ks000.map Prod.fst := by decide +kernel
  have hnd : (ks000.map Prod.fst).Nodup := by decide +kernel
  have hk : ∀ e ∈ ks000, keyIB 2 N e.1 e.2 := by
    intro e he; simp [ks000] at he
  exact zeroTripleS 2 (by decide) N hN 0 0 0 (by decide) (by decide) ks000 hks hnd hk (by decide +kernel)
noncomputable def ks001 : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := []
theorem z001 (N : X2Blocks 2) (hN : ∀ k, (N k)ᵀ = N k)  : ZspecS 2 N 0 0 1 := by
  have hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![0, 0, 1] ↔ k ∈ ks001.map Prod.fst := by decide +kernel
  have hnd : (ks001.map Prod.fst).Nodup := by decide +kernel
  have hk : ∀ e ∈ ks001, keyIB 2 N e.1 e.2 := by
    intro e he; simp [ks001] at he
  exact zeroTripleS 2 (by decide) N hN 0 0 1 (by decide) (by decide) ks001 hks hnd hk (by decide +kernel)
noncomputable def ks002 : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := []
theorem z002 (N : X2Blocks 2) (hN : ∀ k, (N k)ᵀ = N k)  : ZspecS 2 N 0 0 2 := by
  have hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![0, 0, 2] ↔ k ∈ ks002.map Prod.fst := by decide +kernel
  have hnd : (ks002.map Prod.fst).Nodup := by decide +kernel
  have hk : ∀ e ∈ ks002, keyIB 2 N e.1 e.2 := by
    intro e he; simp [ks002] at he
  exact zeroTripleS 2 (by decide) N hN 0 0 2 (by decide) (by decide) ks002 hks hnd hk (by decide +kernel)
def k0 : x2Key 2 := ⟨0, by decide⟩
noncomputable def ks003 : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := [(k0, ([] : List (ℕ × ℕ × ℕ)))]
theorem z003 (N : X2Blocks 2) (hN : ∀ k, (N k)ᵀ = N k) (hN0 : N k0 = x2TrialForm 2 k0) : ZspecS 2 N 0 0 3 := by
  have hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![0, 0, 3] ↔ k ∈ ks003.map Prod.fst := by decide +kernel
  have hnd : (ks003.map Prod.fst).Nodup := by decide +kernel
  have hk : ∀ e ∈ ks003, keyIB 2 N e.1 e.2 := by
    intro e he
    simp only [ks003, List.mem_singleton] at he
    subst he
    exact (keyOK_of_zeroBlock 0 2 N k0 (by rw [hN0]; exact trialForm_zero 2 k0 (by decide))).1
  exact zeroTripleS 2 (by decide) N hN 0 0 3 (by decide) (by decide) ks003 hks hnd hk (by decide +kernel)
def k1 : x2Key 2 := ⟨1, by decide⟩
noncomputable def ks004 : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := [(k1, ([] : List (ℕ × ℕ × ℕ)))]
theorem z004 (N : X2Blocks 2) (hN : ∀ k, (N k)ᵀ = N k) (hN1 : N k1 = x2TrialForm 2 k1) : ZspecS 2 N 0 0 4 := by
  have hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![0, 0, 4] ↔ k ∈ ks004.map Prod.fst := by decide +kernel
  have hnd : (ks004.map Prod.fst).Nodup := by decide +kernel
  have hk : ∀ e ∈ ks004, keyIB 2 N e.1 e.2 := by
    intro e he
    simp only [ks004, List.mem_singleton] at he
    subst he
    exact (keyOK_of_zeroBlock 0 2 N k1 (by rw [hN1]; exact trialForm_zero 2 k1 (by decide))).1
  exact zeroTripleS 2 (by decide) N hN 0 0 4 (by decide) (by decide) ks004 hks hnd hk (by decide +kernel)
theorem z007 (N : X2Blocks 2) : ZspecS 2 N 0 0 7 :=
  zspecS_of_nS 2 N 0 0 7 (by decide)
def k4 : x2Key 2 := ⟨4, by decide⟩
noncomputable def ks011 : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := [(k4, ([] : List (ℕ × ℕ × ℕ)))]
theorem z011 (N : X2Blocks 2) (hN : ∀ k, (N k)ᵀ = N k) (hN4 : N k4 = x2TrialForm 2 k4) : ZspecS 2 N 0 1 1 := by
  have hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![0, 1, 1] ↔ k ∈ ks011.map Prod.fst := by decide +kernel
  have hnd : (ks011.map Prod.fst).Nodup := by decide +kernel
  have hk : ∀ e ∈ ks011, keyIB 2 N e.1 e.2 := by
    intro e he
    simp only [ks011, List.mem_singleton] at he
    subst he
    exact (keyOK_of_zeroBlock 0 2 N k4 (by rw [hN4]; exact trialForm_zero 2 k4 (by decide))).1
  exact zeroTripleS 2 (by decide) N hN 0 1 1 (by decide) (by decide) ks011 hks hnd hk (by decide +kernel)
def k5 : x2Key 2 := ⟨5, by decide⟩
noncomputable def ks012 : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := [(k5, ([] : List (ℕ × ℕ × ℕ)))]
theorem z012 (N : X2Blocks 2) (hN : ∀ k, (N k)ᵀ = N k) (hN5 : N k5 = x2TrialForm 2 k5) : ZspecS 2 N 0 1 2 := by
  have hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![0, 1, 2] ↔ k ∈ ks012.map Prod.fst := by decide +kernel
  have hnd : (ks012.map Prod.fst).Nodup := by decide +kernel
  have hk : ∀ e ∈ ks012, keyIB 2 N e.1 e.2 := by
    intro e he
    simp only [ks012, List.mem_singleton] at he
    subst he
    exact (keyOK_of_zeroBlock 0 2 N k5 (by rw [hN5]; exact trialForm_zero 2 k5 (by decide))).1
  exact zeroTripleS 2 (by decide) N hN 0 1 2 (by decide) (by decide) ks012 hks hnd hk (by decide +kernel)
def k6 : x2Key 2 := ⟨6, by decide⟩
noncomputable def ks013 : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := [(k6, ([] : List (ℕ × ℕ × ℕ)))]
theorem z013 (N : X2Blocks 2) (hN : ∀ k, (N k)ᵀ = N k) (hN6 : N k6 = x2TrialForm 2 k6) : ZspecS 2 N 0 1 3 := by
  have hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![0, 1, 3] ↔ k ∈ ks013.map Prod.fst := by decide +kernel
  have hnd : (ks013.map Prod.fst).Nodup := by decide +kernel
  have hk : ∀ e ∈ ks013, keyIB 2 N e.1 e.2 := by
    intro e he
    simp only [ks013, List.mem_singleton] at he
    subst he
    exact (keyOK_of_zeroBlock 0 2 N k6 (by rw [hN6]; exact trialForm_zero 2 k6 (by decide))).1
  exact zeroTripleS 2 (by decide) N hN 0 1 3 (by decide) (by decide) ks013 hks hnd hk (by decide +kernel)
theorem z017 (N : X2Blocks 2) : ZspecS 2 N 0 1 7 :=
  zspecS_of_nS 2 N 0 1 7 (by decide)
def k10 : x2Key 2 := ⟨10, by decide⟩
noncomputable def ks022 : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := [(k10, ([] : List (ℕ × ℕ × ℕ)))]
theorem z022 (N : X2Blocks 2) (hN : ∀ k, (N k)ᵀ = N k) (hN10 : N k10 = x2TrialForm 2 k10) : ZspecS 2 N 0 2 2 := by
  have hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![0, 2, 2] ↔ k ∈ ks022.map Prod.fst := by decide +kernel
  have hnd : (ks022.map Prod.fst).Nodup := by decide +kernel
  have hk : ∀ e ∈ ks022, keyIB 2 N e.1 e.2 := by
    intro e he
    simp only [ks022, List.mem_singleton] at he
    subst he
    exact (keyOK_of_zeroBlock 0 2 N k10 (by rw [hN10]; exact trialForm_zero 2 k10 (by decide))).1
  exact zeroTripleS 2 (by decide) N hN 0 2 2 (by decide) (by decide) ks022 hks hnd hk (by decide +kernel)
def k11 : x2Key 2 := ⟨11, by decide⟩
noncomputable def ks023 : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := [(k11, ([] : List (ℕ × ℕ × ℕ)))]
theorem z023 (N : X2Blocks 2) (hN : ∀ k, (N k)ᵀ = N k) (hN11 : N k11 = x2TrialForm 2 k11) : ZspecS 2 N 0 2 3 := by
  have hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![0, 2, 3] ↔ k ∈ ks023.map Prod.fst := by decide +kernel
  have hnd : (ks023.map Prod.fst).Nodup := by decide +kernel
  have hk : ∀ e ∈ ks023, keyIB 2 N e.1 e.2 := by
    intro e he
    simp only [ks023, List.mem_singleton] at he
    subst he
    exact (keyOK_of_zeroBlock 0 2 N k11 (by rw [hN11]; exact trialForm_zero 2 k11 (by decide))).1
  exact zeroTripleS 2 (by decide) N hN 0 2 3 (by decide) (by decide) ks023 hks hnd hk (by decide +kernel)
theorem z027 (N : X2Blocks 2) : ZspecS 2 N 0 2 7 :=
  zspecS_of_nS 2 N 0 2 7 (by decide)
def k15 : x2Key 2 := ⟨15, by decide⟩
noncomputable def ks033 : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := [(k15, ([] : List (ℕ × ℕ × ℕ)))]
theorem z033 (N : X2Blocks 2) (hN : ∀ k, (N k)ᵀ = N k) (hN15 : N k15 = x2TrialForm 2 k15) : ZspecS 2 N 0 3 3 := by
  have hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![0, 3, 3] ↔ k ∈ ks033.map Prod.fst := by decide +kernel
  have hnd : (ks033.map Prod.fst).Nodup := by decide +kernel
  have hk : ∀ e ∈ ks033, keyIB 2 N e.1 e.2 := by
    intro e he
    simp only [ks033, List.mem_singleton] at he
    subst he
    exact (keyOK_of_zeroBlock 0 2 N k15 (by rw [hN15]; exact trialForm_zero 2 k15 (by decide))).1
  exact zeroTripleS 2 (by decide) N hN 0 3 3 (by decide) (by decide) ks033 hks hnd hk (by decide +kernel)
theorem z037 (N : X2Blocks 2) : ZspecS 2 N 0 3 7 :=
  zspecS_of_nS 2 N 0 3 7 (by decide)
theorem z047 (N : X2Blocks 2) : ZspecS 2 N 0 4 7 :=
  zspecS_of_nS 2 N 0 4 7 (by decide)
theorem z057 (N : X2Blocks 2) : ZspecS 2 N 0 5 7 :=
  zspecS_of_nS 2 N 0 5 7 (by decide)
theorem z067 (N : X2Blocks 2) : ZspecS 2 N 0 6 7 :=
  zspecS_of_nS 2 N 0 6 7 (by decide)
theorem z077 (N : X2Blocks 2) : ZspecS 2 N 0 7 7 :=
  zspecS_of_nS 2 N 0 7 7 (by decide)
def k28 : x2Key 2 := ⟨28, by decide⟩
def k29 : x2Key 2 := ⟨29, by decide⟩
noncomputable def ks111 : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := [(k28, ([] : List (ℕ × ℕ × ℕ))), (k29, ([] : List (ℕ × ℕ × ℕ)))]
theorem z111 (N : X2Blocks 2) (hN : ∀ k, (N k)ᵀ = N k) (hN28 : N k28 = x2TrialForm 2 k28) (hN29 : N k29 = x2TrialForm 2 k29) : ZspecS 2 N 1 1 1 := by
  have hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![1, 1, 1] ↔ k ∈ ks111.map Prod.fst := by decide +kernel
  have hnd : (ks111.map Prod.fst).Nodup := by decide +kernel
  have hk : ∀ e ∈ ks111, keyIB 2 N e.1 e.2 := by
    intro e he
    simp only [ks111, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact (keyOK_of_zeroBlock 0 2 N k28 (by rw [hN28]; exact trialForm_zero 2 k28 (by decide))).1
    · exact (keyOK_of_zeroBlock 0 2 N k29 (by rw [hN29]; exact trialForm_zero 2 k29 (by decide))).1
  exact zeroTripleS 2 (by decide) N hN 1 1 1 (by decide) (by decide) ks111 hks hnd hk (by decide +kernel)
def k30 : x2Key 2 := ⟨30, by decide⟩
def k31 : x2Key 2 := ⟨31, by decide⟩
noncomputable def ks112 : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := [(k30, ([] : List (ℕ × ℕ × ℕ))), (k31, ([] : List (ℕ × ℕ × ℕ)))]
theorem z112 (N : X2Blocks 2) (hN : ∀ k, (N k)ᵀ = N k) (hN30 : N k30 = x2TrialForm 2 k30) (hN31 : N k31 = x2TrialForm 2 k31) : ZspecS 2 N 1 1 2 := by
  have hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![1, 1, 2] ↔ k ∈ ks112.map Prod.fst := by decide +kernel
  have hnd : (ks112.map Prod.fst).Nodup := by decide +kernel
  have hk : ∀ e ∈ ks112, keyIB 2 N e.1 e.2 := by
    intro e he
    simp only [ks112, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact (keyOK_of_zeroBlock 0 2 N k30 (by rw [hN30]; exact trialForm_zero 2 k30 (by decide))).1
    · exact (keyOK_of_zeroBlock 0 2 N k31 (by rw [hN31]; exact trialForm_zero 2 k31 (by decide))).1
  exact zeroTripleS 2 (by decide) N hN 1 1 2 (by decide) (by decide) ks112 hks hnd hk (by decide +kernel)
def k32 : x2Key 2 := ⟨32, by decide⟩
def k33 : x2Key 2 := ⟨33, by decide⟩
noncomputable def ks113 : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := [(k32, ([] : List (ℕ × ℕ × ℕ))), (k33, ([] : List (ℕ × ℕ × ℕ)))]
theorem z113 (N : X2Blocks 2) (hN : ∀ k, (N k)ᵀ = N k) (hN32 : N k32 = x2TrialForm 2 k32) (hN33 : N k33 = x2TrialForm 2 k33) : ZspecS 2 N 1 1 3 := by
  have hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![1, 1, 3] ↔ k ∈ ks113.map Prod.fst := by decide +kernel
  have hnd : (ks113.map Prod.fst).Nodup := by decide +kernel
  have hk : ∀ e ∈ ks113, keyIB 2 N e.1 e.2 := by
    intro e he
    simp only [ks113, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact (keyOK_of_zeroBlock 0 2 N k32 (by rw [hN32]; exact trialForm_zero 2 k32 (by decide))).1
    · exact (keyOK_of_zeroBlock 0 2 N k33 (by rw [hN33]; exact trialForm_zero 2 k33 (by decide))).1
  exact zeroTripleS 2 (by decide) N hN 1 1 3 (by decide) (by decide) ks113 hks hnd hk (by decide +kernel)
theorem z117 (N : X2Blocks 2) : ZspecS 2 N 1 1 7 :=
  zspecS_of_nS 2 N 1 1 7 (by decide)
def k40 : x2Key 2 := ⟨40, by decide⟩
def k41 : x2Key 2 := ⟨41, by decide⟩
noncomputable def ks122 : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := [(k40, ([] : List (ℕ × ℕ × ℕ))), (k41, ([] : List (ℕ × ℕ × ℕ)))]
theorem z122 (N : X2Blocks 2) (hN : ∀ k, (N k)ᵀ = N k) (hN40 : N k40 = x2TrialForm 2 k40) (hN41 : N k41 = x2TrialForm 2 k41) : ZspecS 2 N 1 2 2 := by
  have hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![1, 2, 2] ↔ k ∈ ks122.map Prod.fst := by decide +kernel
  have hnd : (ks122.map Prod.fst).Nodup := by decide +kernel
  have hk : ∀ e ∈ ks122, keyIB 2 N e.1 e.2 := by
    intro e he
    simp only [ks122, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact (keyOK_of_zeroBlock 0 2 N k40 (by rw [hN40]; exact trialForm_zero 2 k40 (by decide))).1
    · exact (keyOK_of_zeroBlock 0 2 N k41 (by rw [hN41]; exact trialForm_zero 2 k41 (by decide))).1
  exact zeroTripleS 2 (by decide) N hN 1 2 2 (by decide) (by decide) ks122 hks hnd hk (by decide +kernel)
def k42 : x2Key 2 := ⟨42, by decide⟩
noncomputable def ks123 : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := [(k42, ([] : List (ℕ × ℕ × ℕ)))]
theorem z123 (N : X2Blocks 2) (hN : ∀ k, (N k)ᵀ = N k) (hN42 : N k42 = x2TrialForm 2 k42) : ZspecS 2 N 1 2 3 := by
  have hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![1, 2, 3] ↔ k ∈ ks123.map Prod.fst := by decide +kernel
  have hnd : (ks123.map Prod.fst).Nodup := by decide +kernel
  have hk : ∀ e ∈ ks123, keyIB 2 N e.1 e.2 := by
    intro e he
    simp only [ks123, List.mem_singleton] at he
    subst he
    exact (keyOK_of_zeroBlock 0 2 N k42 (by rw [hN42]; exact trialForm_zero 2 k42 (by decide))).1
  exact zeroTripleS 2 (by decide) N hN 1 2 3 (by decide) (by decide) ks123 hks hnd hk (by decide +kernel)
theorem z127 (N : X2Blocks 2) : ZspecS 2 N 1 2 7 :=
  zspecS_of_nS 2 N 1 2 7 (by decide)
def k46 : x2Key 2 := ⟨46, by decide⟩
def k47 : x2Key 2 := ⟨47, by decide⟩
noncomputable def ks133 : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := [(k46, ([] : List (ℕ × ℕ × ℕ))), (k47, ([] : List (ℕ × ℕ × ℕ)))]
theorem z133 (N : X2Blocks 2) (hN : ∀ k, (N k)ᵀ = N k) (hN46 : N k46 = x2TrialForm 2 k46) (hN47 : N k47 = x2TrialForm 2 k47) : ZspecS 2 N 1 3 3 := by
  have hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![1, 3, 3] ↔ k ∈ ks133.map Prod.fst := by decide +kernel
  have hnd : (ks133.map Prod.fst).Nodup := by decide +kernel
  have hk : ∀ e ∈ ks133, keyIB 2 N e.1 e.2 := by
    intro e he
    simp only [ks133, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact (keyOK_of_zeroBlock 0 2 N k46 (by rw [hN46]; exact trialForm_zero 2 k46 (by decide))).1
    · exact (keyOK_of_zeroBlock 0 2 N k47 (by rw [hN47]; exact trialForm_zero 2 k47 (by decide))).1
  exact zeroTripleS 2 (by decide) N hN 1 3 3 (by decide) (by decide) ks133 hks hnd hk (by decide +kernel)
theorem z137 (N : X2Blocks 2) : ZspecS 2 N 1 3 7 :=
  zspecS_of_nS 2 N 1 3 7 (by decide)
theorem z147 (N : X2Blocks 2) : ZspecS 2 N 1 4 7 :=
  zspecS_of_nS 2 N 1 4 7 (by decide)
theorem z157 (N : X2Blocks 2) : ZspecS 2 N 1 5 7 :=
  zspecS_of_nS 2 N 1 5 7 (by decide)
theorem z167 (N : X2Blocks 2) : ZspecS 2 N 1 6 7 :=
  zspecS_of_nS 2 N 1 6 7 (by decide)
theorem z177 (N : X2Blocks 2) : ZspecS 2 N 1 7 7 :=
  zspecS_of_nS 2 N 1 7 7 (by decide)
def k62 : x2Key 2 := ⟨62, by decide⟩
def k63 : x2Key 2 := ⟨63, by decide⟩
noncomputable def ks223 : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := [(k62, ([] : List (ℕ × ℕ × ℕ))), (k63, ([] : List (ℕ × ℕ × ℕ)))]
theorem z223 (N : X2Blocks 2) (hN : ∀ k, (N k)ᵀ = N k) (hN62 : N k62 = x2TrialForm 2 k62) (hN63 : N k63 = x2TrialForm 2 k63) : ZspecS 2 N 2 2 3 := by
  have hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![2, 2, 3] ↔ k ∈ ks223.map Prod.fst := by decide +kernel
  have hnd : (ks223.map Prod.fst).Nodup := by decide +kernel
  have hk : ∀ e ∈ ks223, keyIB 2 N e.1 e.2 := by
    intro e he
    simp only [ks223, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact (keyOK_of_zeroBlock 0 2 N k62 (by rw [hN62]; exact trialForm_zero 2 k62 (by decide))).1
    · exact (keyOK_of_zeroBlock 0 2 N k63 (by rw [hN63]; exact trialForm_zero 2 k63 (by decide))).1
  exact zeroTripleS 2 (by decide) N hN 2 2 3 (by decide) (by decide) ks223 hks hnd hk (by decide +kernel)
theorem z227 (N : X2Blocks 2) : ZspecS 2 N 2 2 7 :=
  zspecS_of_nS 2 N 2 2 7 (by decide)
def k70 : x2Key 2 := ⟨70, by decide⟩
def k71 : x2Key 2 := ⟨71, by decide⟩
noncomputable def ks233 : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := [(k70, ([] : List (ℕ × ℕ × ℕ))), (k71, ([] : List (ℕ × ℕ × ℕ)))]
theorem z233 (N : X2Blocks 2) (hN : ∀ k, (N k)ᵀ = N k) (hN70 : N k70 = x2TrialForm 2 k70) (hN71 : N k71 = x2TrialForm 2 k71) : ZspecS 2 N 2 3 3 := by
  have hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![2, 3, 3] ↔ k ∈ ks233.map Prod.fst := by decide +kernel
  have hnd : (ks233.map Prod.fst).Nodup := by decide +kernel
  have hk : ∀ e ∈ ks233, keyIB 2 N e.1 e.2 := by
    intro e he
    simp only [ks233, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact (keyOK_of_zeroBlock 0 2 N k70 (by rw [hN70]; exact trialForm_zero 2 k70 (by decide))).1
    · exact (keyOK_of_zeroBlock 0 2 N k71 (by rw [hN71]; exact trialForm_zero 2 k71 (by decide))).1
  exact zeroTripleS 2 (by decide) N hN 2 3 3 (by decide) (by decide) ks233 hks hnd hk (by decide +kernel)
theorem z237 (N : X2Blocks 2) : ZspecS 2 N 2 3 7 :=
  zspecS_of_nS 2 N 2 3 7 (by decide)
theorem z247 (N : X2Blocks 2) : ZspecS 2 N 2 4 7 :=
  zspecS_of_nS 2 N 2 4 7 (by decide)
theorem z257 (N : X2Blocks 2) : ZspecS 2 N 2 5 7 :=
  zspecS_of_nS 2 N 2 5 7 (by decide)
theorem z267 (N : X2Blocks 2) : ZspecS 2 N 2 6 7 :=
  zspecS_of_nS 2 N 2 6 7 (by decide)
theorem z277 (N : X2Blocks 2) : ZspecS 2 N 2 7 7 :=
  zspecS_of_nS 2 N 2 7 7 (by decide)
def k84 : x2Key 2 := ⟨84, by decide⟩
def k85 : x2Key 2 := ⟨85, by decide⟩
noncomputable def ks333 : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := [(k84, ([] : List (ℕ × ℕ × ℕ))), (k85, ([] : List (ℕ × ℕ × ℕ)))]
theorem z333 (N : X2Blocks 2) (hN : ∀ k, (N k)ᵀ = N k) (hN84 : N k84 = x2TrialForm 2 k84) (hN85 : N k85 = x2TrialForm 2 k85) : ZspecS 2 N 3 3 3 := by
  have hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![3, 3, 3] ↔ k ∈ ks333.map Prod.fst := by decide +kernel
  have hnd : (ks333.map Prod.fst).Nodup := by decide +kernel
  have hk : ∀ e ∈ ks333, keyIB 2 N e.1 e.2 := by
    intro e he
    simp only [ks333, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact (keyOK_of_zeroBlock 0 2 N k84 (by rw [hN84]; exact trialForm_zero 2 k84 (by decide))).1
    · exact (keyOK_of_zeroBlock 0 2 N k85 (by rw [hN85]; exact trialForm_zero 2 k85 (by decide))).1
  exact zeroTripleS 2 (by decide) N hN 3 3 3 (by decide) (by decide) ks333 hks hnd hk (by decide +kernel)
theorem z337 (N : X2Blocks 2) : ZspecS 2 N 3 3 7 :=
  zspecS_of_nS 2 N 3 3 7 (by decide)
theorem z347 (N : X2Blocks 2) : ZspecS 2 N 3 4 7 :=
  zspecS_of_nS 2 N 3 4 7 (by decide)
theorem z357 (N : X2Blocks 2) : ZspecS 2 N 3 5 7 :=
  zspecS_of_nS 2 N 3 5 7 (by decide)
theorem z367 (N : X2Blocks 2) : ZspecS 2 N 3 6 7 :=
  zspecS_of_nS 2 N 3 6 7 (by decide)
theorem z377 (N : X2Blocks 2) : ZspecS 2 N 3 7 7 :=
  zspecS_of_nS 2 N 3 7 7 (by decide)
theorem z447 (N : X2Blocks 2) : ZspecS 2 N 4 4 7 :=
  zspecS_of_nS 2 N 4 4 7 (by decide)
theorem z457 (N : X2Blocks 2) : ZspecS 2 N 4 5 7 :=
  zspecS_of_nS 2 N 4 5 7 (by decide)
theorem z467 (N : X2Blocks 2) : ZspecS 2 N 4 6 7 :=
  zspecS_of_nS 2 N 4 6 7 (by decide)
theorem z477 (N : X2Blocks 2) : ZspecS 2 N 4 7 7 :=
  zspecS_of_nS 2 N 4 7 7 (by decide)
theorem z557 (N : X2Blocks 2) : ZspecS 2 N 5 5 7 :=
  zspecS_of_nS 2 N 5 5 7 (by decide)
theorem z567 (N : X2Blocks 2) : ZspecS 2 N 5 6 7 :=
  zspecS_of_nS 2 N 5 6 7 (by decide)
theorem z577 (N : X2Blocks 2) : ZspecS 2 N 5 7 7 :=
  zspecS_of_nS 2 N 5 7 7 (by decide)
theorem z667 (N : X2Blocks 2) : ZspecS 2 N 6 6 7 :=
  zspecS_of_nS 2 N 6 6 7 (by decide)
theorem z677 (N : X2Blocks 2) : ZspecS 2 N 6 7 7 :=
  zspecS_of_nS 2 N 6 7 7 (by decide)
theorem z777 (N : X2Blocks 2) : ZspecS 2 N 7 7 7 :=
  zspecS_of_nS 2 N 7 7 7 (by decide)

end ThreeCopyQutritWerner.X2.InZS2
