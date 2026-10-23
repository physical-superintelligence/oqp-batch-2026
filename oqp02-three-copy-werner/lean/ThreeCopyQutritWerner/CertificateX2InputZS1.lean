module

public import ThreeCopyQutritWerner.CertificateX2InputLab

@[expose] public section


/-! The sorted type triples of sector 1 whose keys contribute no part (or with a type of multiplicity 0): x2EmbedS vanishes on their labels. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InZS1
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

noncomputable def ks000 : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := []
theorem z000 (N : X2Blocks 1) (hN : ∀ k, (N k)ᵀ = N k)  : ZspecS 1 N 0 0 0 := by
  have hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![0, 0, 0] ↔ k ∈ ks000.map Prod.fst := by decide +kernel
  have hnd : (ks000.map Prod.fst).Nodup := by decide +kernel
  have hk : ∀ e ∈ ks000, keyIB 1 N e.1 e.2 := by
    intro e he; simp [ks000] at he
  exact zeroTripleS 1 (by decide) N hN 0 0 0 (by decide) (by decide) ks000 hks hnd hk (by decide +kernel)
noncomputable def ks001 : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := []
theorem z001 (N : X2Blocks 1) (hN : ∀ k, (N k)ᵀ = N k)  : ZspecS 1 N 0 0 1 := by
  have hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![0, 0, 1] ↔ k ∈ ks001.map Prod.fst := by decide +kernel
  have hnd : (ks001.map Prod.fst).Nodup := by decide +kernel
  have hk : ∀ e ∈ ks001, keyIB 1 N e.1 e.2 := by
    intro e he; simp [ks001] at he
  exact zeroTripleS 1 (by decide) N hN 0 0 1 (by decide) (by decide) ks001 hks hnd hk (by decide +kernel)
noncomputable def ks002 : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := []
theorem z002 (N : X2Blocks 1) (hN : ∀ k, (N k)ᵀ = N k)  : ZspecS 1 N 0 0 2 := by
  have hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![0, 0, 2] ↔ k ∈ ks002.map Prod.fst := by decide +kernel
  have hnd : (ks002.map Prod.fst).Nodup := by decide +kernel
  have hk : ∀ e ∈ ks002, keyIB 1 N e.1 e.2 := by
    intro e he; simp [ks002] at he
  exact zeroTripleS 1 (by decide) N hN 0 0 2 (by decide) (by decide) ks002 hks hnd hk (by decide +kernel)
def k0 : x2Key 1 := ⟨0, by decide⟩
noncomputable def ks003 : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k0, ([] : List (ℕ × ℕ × ℕ)))]
theorem z003 (N : X2Blocks 1) (hN : ∀ k, (N k)ᵀ = N k) (hN0 : N k0 = x2TrialForm 1 k0) : ZspecS 1 N 0 0 3 := by
  have hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![0, 0, 3] ↔ k ∈ ks003.map Prod.fst := by decide +kernel
  have hnd : (ks003.map Prod.fst).Nodup := by decide +kernel
  have hk : ∀ e ∈ ks003, keyIB 1 N e.1 e.2 := by
    intro e he
    simp only [ks003, List.mem_singleton] at he
    subst he
    exact (keyOK_of_zeroBlock 0 1 N k0 (by rw [hN0]; exact trialForm_zero 1 k0 (by decide))).1
  exact zeroTripleS 1 (by decide) N hN 0 0 3 (by decide) (by decide) ks003 hks hnd hk (by decide +kernel)
def k1 : x2Key 1 := ⟨1, by decide⟩
noncomputable def ks004 : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k1, ([] : List (ℕ × ℕ × ℕ)))]
theorem z004 (N : X2Blocks 1) (hN : ∀ k, (N k)ᵀ = N k) (hN1 : N k1 = x2TrialForm 1 k1) : ZspecS 1 N 0 0 4 := by
  have hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![0, 0, 4] ↔ k ∈ ks004.map Prod.fst := by decide +kernel
  have hnd : (ks004.map Prod.fst).Nodup := by decide +kernel
  have hk : ∀ e ∈ ks004, keyIB 1 N e.1 e.2 := by
    intro e he
    simp only [ks004, List.mem_singleton] at he
    subst he
    exact (keyOK_of_zeroBlock 0 1 N k1 (by rw [hN1]; exact trialForm_zero 1 k1 (by decide))).1
  exact zeroTripleS 1 (by decide) N hN 0 0 4 (by decide) (by decide) ks004 hks hnd hk (by decide +kernel)
def k2 : x2Key 1 := ⟨2, by decide⟩
noncomputable def ks005 : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k2, ([] : List (ℕ × ℕ × ℕ)))]
theorem z005 (N : X2Blocks 1) (hN : ∀ k, (N k)ᵀ = N k) (hN2 : N k2 = x2TrialForm 1 k2) : ZspecS 1 N 0 0 5 := by
  have hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![0, 0, 5] ↔ k ∈ ks005.map Prod.fst := by decide +kernel
  have hnd : (ks005.map Prod.fst).Nodup := by decide +kernel
  have hk : ∀ e ∈ ks005, keyIB 1 N e.1 e.2 := by
    intro e he
    simp only [ks005, List.mem_singleton] at he
    subst he
    exact (keyOK_of_zeroBlock 0 1 N k2 (by rw [hN2]; exact trialForm_zero 1 k2 (by decide))).1
  exact zeroTripleS 1 (by decide) N hN 0 0 5 (by decide) (by decide) ks005 hks hnd hk (by decide +kernel)
def k4 : x2Key 1 := ⟨4, by decide⟩
noncomputable def ks007 : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k4, ([] : List (ℕ × ℕ × ℕ)))]
theorem z007 (N : X2Blocks 1) (hN : ∀ k, (N k)ᵀ = N k) (hN4 : N k4 = x2TrialForm 1 k4) : ZspecS 1 N 0 0 7 := by
  have hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![0, 0, 7] ↔ k ∈ ks007.map Prod.fst := by decide +kernel
  have hnd : (ks007.map Prod.fst).Nodup := by decide +kernel
  have hk : ∀ e ∈ ks007, keyIB 1 N e.1 e.2 := by
    intro e he
    simp only [ks007, List.mem_singleton] at he
    subst he
    exact (keyOK_of_zeroBlock 0 1 N k4 (by rw [hN4]; exact trialForm_zero 1 k4 (by decide))).1
  exact zeroTripleS 1 (by decide) N hN 0 0 7 (by decide) (by decide) ks007 hks hnd hk (by decide +kernel)
noncomputable def ks011 : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := []
theorem z011 (N : X2Blocks 1) (hN : ∀ k, (N k)ᵀ = N k)  : ZspecS 1 N 0 1 1 := by
  have hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![0, 1, 1] ↔ k ∈ ks011.map Prod.fst := by decide +kernel
  have hnd : (ks011.map Prod.fst).Nodup := by decide +kernel
  have hk : ∀ e ∈ ks011, keyIB 1 N e.1 e.2 := by
    intro e he; simp [ks011] at he
  exact zeroTripleS 1 (by decide) N hN 0 1 1 (by decide) (by decide) ks011 hks hnd hk (by decide +kernel)
def k5 : x2Key 1 := ⟨5, by decide⟩
noncomputable def ks012 : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k5, ([] : List (ℕ × ℕ × ℕ)))]
theorem z012 (N : X2Blocks 1) (hN : ∀ k, (N k)ᵀ = N k) (hN5 : N k5 = x2TrialForm 1 k5) : ZspecS 1 N 0 1 2 := by
  have hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![0, 1, 2] ↔ k ∈ ks012.map Prod.fst := by decide +kernel
  have hnd : (ks012.map Prod.fst).Nodup := by decide +kernel
  have hk : ∀ e ∈ ks012, keyIB 1 N e.1 e.2 := by
    intro e he
    simp only [ks012, List.mem_singleton] at he
    subst he
    exact (keyOK_of_zeroBlock 0 1 N k5 (by rw [hN5]; exact trialForm_zero 1 k5 (by decide))).1
  exact zeroTripleS 1 (by decide) N hN 0 1 2 (by decide) (by decide) ks012 hks hnd hk (by decide +kernel)
def k6 : x2Key 1 := ⟨6, by decide⟩
noncomputable def ks013 : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k6, ([] : List (ℕ × ℕ × ℕ)))]
theorem z013 (N : X2Blocks 1) (hN : ∀ k, (N k)ᵀ = N k) (hN6 : N k6 = x2TrialForm 1 k6) : ZspecS 1 N 0 1 3 := by
  have hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![0, 1, 3] ↔ k ∈ ks013.map Prod.fst := by decide +kernel
  have hnd : (ks013.map Prod.fst).Nodup := by decide +kernel
  have hk : ∀ e ∈ ks013, keyIB 1 N e.1 e.2 := by
    intro e he
    simp only [ks013, List.mem_singleton] at he
    subst he
    exact (keyOK_of_zeroBlock 0 1 N k6 (by rw [hN6]; exact trialForm_zero 1 k6 (by decide))).1
  exact zeroTripleS 1 (by decide) N hN 0 1 3 (by decide) (by decide) ks013 hks hnd hk (by decide +kernel)
def k7 : x2Key 1 := ⟨7, by decide⟩
noncomputable def ks014 : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k7, ([] : List (ℕ × ℕ × ℕ)))]
theorem z014 (N : X2Blocks 1) (hN : ∀ k, (N k)ᵀ = N k) (hN7 : N k7 = x2TrialForm 1 k7) : ZspecS 1 N 0 1 4 := by
  have hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![0, 1, 4] ↔ k ∈ ks014.map Prod.fst := by decide +kernel
  have hnd : (ks014.map Prod.fst).Nodup := by decide +kernel
  have hk : ∀ e ∈ ks014, keyIB 1 N e.1 e.2 := by
    intro e he
    simp only [ks014, List.mem_singleton] at he
    subst he
    exact (keyOK_of_zeroBlock 0 1 N k7 (by rw [hN7]; exact trialForm_zero 1 k7 (by decide))).1
  exact zeroTripleS 1 (by decide) N hN 0 1 4 (by decide) (by decide) ks014 hks hnd hk (by decide +kernel)
def k8 : x2Key 1 := ⟨8, by decide⟩
noncomputable def ks015 : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k8, ([] : List (ℕ × ℕ × ℕ)))]
theorem z015 (N : X2Blocks 1) (hN : ∀ k, (N k)ᵀ = N k) (hN8 : N k8 = x2TrialForm 1 k8) : ZspecS 1 N 0 1 5 := by
  have hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![0, 1, 5] ↔ k ∈ ks015.map Prod.fst := by decide +kernel
  have hnd : (ks015.map Prod.fst).Nodup := by decide +kernel
  have hk : ∀ e ∈ ks015, keyIB 1 N e.1 e.2 := by
    intro e he
    simp only [ks015, List.mem_singleton] at he
    subst he
    exact (keyOK_of_zeroBlock 0 1 N k8 (by rw [hN8]; exact trialForm_zero 1 k8 (by decide))).1
  exact zeroTripleS 1 (by decide) N hN 0 1 5 (by decide) (by decide) ks015 hks hnd hk (by decide +kernel)
def k10 : x2Key 1 := ⟨10, by decide⟩
noncomputable def ks017 : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k10, ([] : List (ℕ × ℕ × ℕ)))]
theorem z017 (N : X2Blocks 1) (hN : ∀ k, (N k)ᵀ = N k) (hN10 : N k10 = x2TrialForm 1 k10) : ZspecS 1 N 0 1 7 := by
  have hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![0, 1, 7] ↔ k ∈ ks017.map Prod.fst := by decide +kernel
  have hnd : (ks017.map Prod.fst).Nodup := by decide +kernel
  have hk : ∀ e ∈ ks017, keyIB 1 N e.1 e.2 := by
    intro e he
    simp only [ks017, List.mem_singleton] at he
    subst he
    exact (keyOK_of_zeroBlock 0 1 N k10 (by rw [hN10]; exact trialForm_zero 1 k10 (by decide))).1
  exact zeroTripleS 1 (by decide) N hN 0 1 7 (by decide) (by decide) ks017 hks hnd hk (by decide +kernel)
noncomputable def ks022 : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := []
theorem z022 (N : X2Blocks 1) (hN : ∀ k, (N k)ᵀ = N k)  : ZspecS 1 N 0 2 2 := by
  have hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![0, 2, 2] ↔ k ∈ ks022.map Prod.fst := by decide +kernel
  have hnd : (ks022.map Prod.fst).Nodup := by decide +kernel
  have hk : ∀ e ∈ ks022, keyIB 1 N e.1 e.2 := by
    intro e he; simp [ks022] at he
  exact zeroTripleS 1 (by decide) N hN 0 2 2 (by decide) (by decide) ks022 hks hnd hk (by decide +kernel)
def k11 : x2Key 1 := ⟨11, by decide⟩
noncomputable def ks023 : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k11, ([] : List (ℕ × ℕ × ℕ)))]
theorem z023 (N : X2Blocks 1) (hN : ∀ k, (N k)ᵀ = N k) (hN11 : N k11 = x2TrialForm 1 k11) : ZspecS 1 N 0 2 3 := by
  have hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![0, 2, 3] ↔ k ∈ ks023.map Prod.fst := by decide +kernel
  have hnd : (ks023.map Prod.fst).Nodup := by decide +kernel
  have hk : ∀ e ∈ ks023, keyIB 1 N e.1 e.2 := by
    intro e he
    simp only [ks023, List.mem_singleton] at he
    subst he
    exact (keyOK_of_zeroBlock 0 1 N k11 (by rw [hN11]; exact trialForm_zero 1 k11 (by decide))).1
  exact zeroTripleS 1 (by decide) N hN 0 2 3 (by decide) (by decide) ks023 hks hnd hk (by decide +kernel)
def k13 : x2Key 1 := ⟨13, by decide⟩
noncomputable def ks025 : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k13, ([] : List (ℕ × ℕ × ℕ)))]
theorem z025 (N : X2Blocks 1) (hN : ∀ k, (N k)ᵀ = N k) (hN13 : N k13 = x2TrialForm 1 k13) : ZspecS 1 N 0 2 5 := by
  have hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![0, 2, 5] ↔ k ∈ ks025.map Prod.fst := by decide +kernel
  have hnd : (ks025.map Prod.fst).Nodup := by decide +kernel
  have hk : ∀ e ∈ ks025, keyIB 1 N e.1 e.2 := by
    intro e he
    simp only [ks025, List.mem_singleton] at he
    subst he
    exact (keyOK_of_zeroBlock 0 1 N k13 (by rw [hN13]; exact trialForm_zero 1 k13 (by decide))).1
  exact zeroTripleS 1 (by decide) N hN 0 2 5 (by decide) (by decide) ks025 hks hnd hk (by decide +kernel)
def k16 : x2Key 1 := ⟨16, by decide⟩
def k17 : x2Key 1 := ⟨17, by decide⟩
noncomputable def ks033 : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k16, ([] : List (ℕ × ℕ × ℕ))), (k17, ([] : List (ℕ × ℕ × ℕ)))]
theorem z033 (N : X2Blocks 1) (hN : ∀ k, (N k)ᵀ = N k) (hN16 : N k16 = x2TrialForm 1 k16) (hN17 : N k17 = x2TrialForm 1 k17) : ZspecS 1 N 0 3 3 := by
  have hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![0, 3, 3] ↔ k ∈ ks033.map Prod.fst := by decide +kernel
  have hnd : (ks033.map Prod.fst).Nodup := by decide +kernel
  have hk : ∀ e ∈ ks033, keyIB 1 N e.1 e.2 := by
    intro e he
    simp only [ks033, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact (keyOK_of_zeroBlock 0 1 N k16 (by rw [hN16]; exact trialForm_zero 1 k16 (by decide))).1
    · exact (keyOK_of_zeroBlock 0 1 N k17 (by rw [hN17]; exact trialForm_zero 1 k17 (by decide))).1
  exact zeroTripleS 1 (by decide) N hN 0 3 3 (by decide) (by decide) ks033 hks hnd hk (by decide +kernel)
noncomputable def ks111 : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := []
theorem z111 (N : X2Blocks 1) (hN : ∀ k, (N k)ᵀ = N k)  : ZspecS 1 N 1 1 1 := by
  have hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![1, 1, 1] ↔ k ∈ ks111.map Prod.fst := by decide +kernel
  have hnd : (ks111.map Prod.fst).Nodup := by decide +kernel
  have hk : ∀ e ∈ ks111, keyIB 1 N e.1 e.2 := by
    intro e he; simp [ks111] at he
  exact zeroTripleS 1 (by decide) N hN 1 1 1 (by decide) (by decide) ks111 hks hnd hk (by decide +kernel)
def k36 : x2Key 1 := ⟨36, by decide⟩
def k37 : x2Key 1 := ⟨37, by decide⟩
noncomputable def ks112 : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k36, ([] : List (ℕ × ℕ × ℕ))), (k37, ([] : List (ℕ × ℕ × ℕ)))]
theorem z112 (N : X2Blocks 1) (hN : ∀ k, (N k)ᵀ = N k) (hN36 : N k36 = x2TrialForm 1 k36) (hN37 : N k37 = x2TrialForm 1 k37) : ZspecS 1 N 1 1 2 := by
  have hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![1, 1, 2] ↔ k ∈ ks112.map Prod.fst := by decide +kernel
  have hnd : (ks112.map Prod.fst).Nodup := by decide +kernel
  have hk : ∀ e ∈ ks112, keyIB 1 N e.1 e.2 := by
    intro e he
    simp only [ks112, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact (keyOK_of_zeroBlock 0 1 N k36 (by rw [hN36]; exact trialForm_zero 1 k36 (by decide))).1
    · exact (keyOK_of_zeroBlock 0 1 N k37 (by rw [hN37]; exact trialForm_zero 1 k37 (by decide))).1
  exact zeroTripleS 1 (by decide) N hN 1 1 2 (by decide) (by decide) ks112 hks hnd hk (by decide +kernel)
def k38 : x2Key 1 := ⟨38, by decide⟩
def k39 : x2Key 1 := ⟨39, by decide⟩
noncomputable def ks113 : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k38, ([] : List (ℕ × ℕ × ℕ))), (k39, ([] : List (ℕ × ℕ × ℕ)))]
theorem z113 (N : X2Blocks 1) (hN : ∀ k, (N k)ᵀ = N k) (hN38 : N k38 = x2TrialForm 1 k38) (hN39 : N k39 = x2TrialForm 1 k39) : ZspecS 1 N 1 1 3 := by
  have hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![1, 1, 3] ↔ k ∈ ks113.map Prod.fst := by decide +kernel
  have hnd : (ks113.map Prod.fst).Nodup := by decide +kernel
  have hk : ∀ e ∈ ks113, keyIB 1 N e.1 e.2 := by
    intro e he
    simp only [ks113, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact (keyOK_of_zeroBlock 0 1 N k38 (by rw [hN38]; exact trialForm_zero 1 k38 (by decide))).1
    · exact (keyOK_of_zeroBlock 0 1 N k39 (by rw [hN39]; exact trialForm_zero 1 k39 (by decide))).1
  exact zeroTripleS 1 (by decide) N hN 1 1 3 (by decide) (by decide) ks113 hks hnd hk (by decide +kernel)
def k40 : x2Key 1 := ⟨40, by decide⟩
def k41 : x2Key 1 := ⟨41, by decide⟩
noncomputable def ks114 : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k40, ([] : List (ℕ × ℕ × ℕ))), (k41, ([] : List (ℕ × ℕ × ℕ)))]
theorem z114 (N : X2Blocks 1) (hN : ∀ k, (N k)ᵀ = N k) (hN40 : N k40 = x2TrialForm 1 k40) (hN41 : N k41 = x2TrialForm 1 k41) : ZspecS 1 N 1 1 4 := by
  have hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![1, 1, 4] ↔ k ∈ ks114.map Prod.fst := by decide +kernel
  have hnd : (ks114.map Prod.fst).Nodup := by decide +kernel
  have hk : ∀ e ∈ ks114, keyIB 1 N e.1 e.2 := by
    intro e he
    simp only [ks114, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact (keyOK_of_zeroBlock 0 1 N k40 (by rw [hN40]; exact trialForm_zero 1 k40 (by decide))).1
    · exact (keyOK_of_zeroBlock 0 1 N k41 (by rw [hN41]; exact trialForm_zero 1 k41 (by decide))).1
  exact zeroTripleS 1 (by decide) N hN 1 1 4 (by decide) (by decide) ks114 hks hnd hk (by decide +kernel)
def k42 : x2Key 1 := ⟨42, by decide⟩
def k43 : x2Key 1 := ⟨43, by decide⟩
noncomputable def ks115 : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k42, ([] : List (ℕ × ℕ × ℕ))), (k43, ([] : List (ℕ × ℕ × ℕ)))]
theorem z115 (N : X2Blocks 1) (hN : ∀ k, (N k)ᵀ = N k) (hN42 : N k42 = x2TrialForm 1 k42) (hN43 : N k43 = x2TrialForm 1 k43) : ZspecS 1 N 1 1 5 := by
  have hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![1, 1, 5] ↔ k ∈ ks115.map Prod.fst := by decide +kernel
  have hnd : (ks115.map Prod.fst).Nodup := by decide +kernel
  have hk : ∀ e ∈ ks115, keyIB 1 N e.1 e.2 := by
    intro e he
    simp only [ks115, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact (keyOK_of_zeroBlock 0 1 N k42 (by rw [hN42]; exact trialForm_zero 1 k42 (by decide))).1
    · exact (keyOK_of_zeroBlock 0 1 N k43 (by rw [hN43]; exact trialForm_zero 1 k43 (by decide))).1
  exact zeroTripleS 1 (by decide) N hN 1 1 5 (by decide) (by decide) ks115 hks hnd hk (by decide +kernel)
def k46 : x2Key 1 := ⟨46, by decide⟩
def k47 : x2Key 1 := ⟨47, by decide⟩
noncomputable def ks117 : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k46, ([] : List (ℕ × ℕ × ℕ))), (k47, ([] : List (ℕ × ℕ × ℕ)))]
theorem z117 (N : X2Blocks 1) (hN : ∀ k, (N k)ᵀ = N k) (hN46 : N k46 = x2TrialForm 1 k46) (hN47 : N k47 = x2TrialForm 1 k47) : ZspecS 1 N 1 1 7 := by
  have hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![1, 1, 7] ↔ k ∈ ks117.map Prod.fst := by decide +kernel
  have hnd : (ks117.map Prod.fst).Nodup := by decide +kernel
  have hk : ∀ e ∈ ks117, keyIB 1 N e.1 e.2 := by
    intro e he
    simp only [ks117, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact (keyOK_of_zeroBlock 0 1 N k46 (by rw [hN46]; exact trialForm_zero 1 k46 (by decide))).1
    · exact (keyOK_of_zeroBlock 0 1 N k47 (by rw [hN47]; exact trialForm_zero 1 k47 (by decide))).1
  exact zeroTripleS 1 (by decide) N hN 1 1 7 (by decide) (by decide) ks117 hks hnd hk (by decide +kernel)
def k48 : x2Key 1 := ⟨48, by decide⟩
noncomputable def ks122 : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k48, ([] : List (ℕ × ℕ × ℕ)))]
theorem z122 (N : X2Blocks 1) (hN : ∀ k, (N k)ᵀ = N k) (hN48 : N k48 = x2TrialForm 1 k48) : ZspecS 1 N 1 2 2 := by
  have hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![1, 2, 2] ↔ k ∈ ks122.map Prod.fst := by decide +kernel
  have hnd : (ks122.map Prod.fst).Nodup := by decide +kernel
  have hk : ∀ e ∈ ks122, keyIB 1 N e.1 e.2 := by
    intro e he
    simp only [ks122, List.mem_singleton] at he
    subst he
    exact (keyOK_of_zeroBlock 0 1 N k48 (by rw [hN48]; exact trialForm_zero 1 k48 (by decide))).1
  exact zeroTripleS 1 (by decide) N hN 1 2 2 (by decide) (by decide) ks122 hks hnd hk (by decide +kernel)
def k49 : x2Key 1 := ⟨49, by decide⟩
noncomputable def ks123 : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k49, ([] : List (ℕ × ℕ × ℕ)))]
theorem z123 (N : X2Blocks 1) (hN : ∀ k, (N k)ᵀ = N k) (hN49 : N k49 = x2TrialForm 1 k49) : ZspecS 1 N 1 2 3 := by
  have hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![1, 2, 3] ↔ k ∈ ks123.map Prod.fst := by decide +kernel
  have hnd : (ks123.map Prod.fst).Nodup := by decide +kernel
  have hk : ∀ e ∈ ks123, keyIB 1 N e.1 e.2 := by
    intro e he
    simp only [ks123, List.mem_singleton] at he
    subst he
    exact (keyOK_of_zeroBlock 0 1 N k49 (by rw [hN49]; exact trialForm_zero 1 k49 (by decide))).1
  exact zeroTripleS 1 (by decide) N hN 1 2 3 (by decide) (by decide) ks123 hks hnd hk (by decide +kernel)
def k54 : x2Key 1 := ⟨54, by decide⟩
def k55 : x2Key 1 := ⟨55, by decide⟩
noncomputable def ks133 : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k54, ([] : List (ℕ × ℕ × ℕ))), (k55, ([] : List (ℕ × ℕ × ℕ)))]
theorem z133 (N : X2Blocks 1) (hN : ∀ k, (N k)ᵀ = N k) (hN54 : N k54 = x2TrialForm 1 k54) (hN55 : N k55 = x2TrialForm 1 k55) : ZspecS 1 N 1 3 3 := by
  have hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![1, 3, 3] ↔ k ∈ ks133.map Prod.fst := by decide +kernel
  have hnd : (ks133.map Prod.fst).Nodup := by decide +kernel
  have hk : ∀ e ∈ ks133, keyIB 1 N e.1 e.2 := by
    intro e he
    simp only [ks133, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact (keyOK_of_zeroBlock 0 1 N k54 (by rw [hN54]; exact trialForm_zero 1 k54 (by decide))).1
    · exact (keyOK_of_zeroBlock 0 1 N k55 (by rw [hN55]; exact trialForm_zero 1 k55 (by decide))).1
  exact zeroTripleS 1 (by decide) N hN 1 3 3 (by decide) (by decide) ks133 hks hnd hk (by decide +kernel)
noncomputable def ks222 : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := []
theorem z222 (N : X2Blocks 1) (hN : ∀ k, (N k)ᵀ = N k)  : ZspecS 1 N 2 2 2 := by
  have hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![2, 2, 2] ↔ k ∈ ks222.map Prod.fst := by decide +kernel
  have hnd : (ks222.map Prod.fst).Nodup := by decide +kernel
  have hk : ∀ e ∈ ks222, keyIB 1 N e.1 e.2 := by
    intro e he; simp [ks222] at he
  exact zeroTripleS 1 (by decide) N hN 2 2 2 (by decide) (by decide) ks222 hks hnd hk (by decide +kernel)
def k74 : x2Key 1 := ⟨74, by decide⟩
def k75 : x2Key 1 := ⟨75, by decide⟩
noncomputable def ks223 : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k74, ([] : List (ℕ × ℕ × ℕ))), (k75, ([] : List (ℕ × ℕ × ℕ)))]
theorem z223 (N : X2Blocks 1) (hN : ∀ k, (N k)ᵀ = N k) (hN74 : N k74 = x2TrialForm 1 k74) (hN75 : N k75 = x2TrialForm 1 k75) : ZspecS 1 N 2 2 3 := by
  have hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![2, 2, 3] ↔ k ∈ ks223.map Prod.fst := by decide +kernel
  have hnd : (ks223.map Prod.fst).Nodup := by decide +kernel
  have hk : ∀ e ∈ ks223, keyIB 1 N e.1 e.2 := by
    intro e he
    simp only [ks223, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact (keyOK_of_zeroBlock 0 1 N k74 (by rw [hN74]; exact trialForm_zero 1 k74 (by decide))).1
    · exact (keyOK_of_zeroBlock 0 1 N k75 (by rw [hN75]; exact trialForm_zero 1 k75 (by decide))).1
  exact zeroTripleS 1 (by decide) N hN 2 2 3 (by decide) (by decide) ks223 hks hnd hk (by decide +kernel)
def k78 : x2Key 1 := ⟨78, by decide⟩
def k79 : x2Key 1 := ⟨79, by decide⟩
noncomputable def ks225 : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k78, ([] : List (ℕ × ℕ × ℕ))), (k79, ([] : List (ℕ × ℕ × ℕ)))]
theorem z225 (N : X2Blocks 1) (hN : ∀ k, (N k)ᵀ = N k) (hN78 : N k78 = x2TrialForm 1 k78) (hN79 : N k79 = x2TrialForm 1 k79) : ZspecS 1 N 2 2 5 := by
  have hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![2, 2, 5] ↔ k ∈ ks225.map Prod.fst := by decide +kernel
  have hnd : (ks225.map Prod.fst).Nodup := by decide +kernel
  have hk : ∀ e ∈ ks225, keyIB 1 N e.1 e.2 := by
    intro e he
    simp only [ks225, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact (keyOK_of_zeroBlock 0 1 N k78 (by rw [hN78]; exact trialForm_zero 1 k78 (by decide))).1
    · exact (keyOK_of_zeroBlock 0 1 N k79 (by rw [hN79]; exact trialForm_zero 1 k79 (by decide))).1
  exact zeroTripleS 1 (by decide) N hN 2 2 5 (by decide) (by decide) ks225 hks hnd hk (by decide +kernel)
def k84 : x2Key 1 := ⟨84, by decide⟩
def k85 : x2Key 1 := ⟨85, by decide⟩
noncomputable def ks233 : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k84, ([] : List (ℕ × ℕ × ℕ))), (k85, ([] : List (ℕ × ℕ × ℕ)))]
theorem z233 (N : X2Blocks 1) (hN : ∀ k, (N k)ᵀ = N k) (hN84 : N k84 = x2TrialForm 1 k84) (hN85 : N k85 = x2TrialForm 1 k85) : ZspecS 1 N 2 3 3 := by
  have hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![2, 3, 3] ↔ k ∈ ks233.map Prod.fst := by decide +kernel
  have hnd : (ks233.map Prod.fst).Nodup := by decide +kernel
  have hk : ∀ e ∈ ks233, keyIB 1 N e.1 e.2 := by
    intro e he
    simp only [ks233, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact (keyOK_of_zeroBlock 0 1 N k84 (by rw [hN84]; exact trialForm_zero 1 k84 (by decide))).1
    · exact (keyOK_of_zeroBlock 0 1 N k85 (by rw [hN85]; exact trialForm_zero 1 k85 (by decide))).1
  exact zeroTripleS 1 (by decide) N hN 2 3 3 (by decide) (by decide) ks233 hks hnd hk (by decide +kernel)

end ThreeCopyQutritWerner.X2.InZS1
