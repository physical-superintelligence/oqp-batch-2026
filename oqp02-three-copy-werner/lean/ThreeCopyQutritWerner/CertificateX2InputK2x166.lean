module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (1, 6, 6) of sector 2, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK2x166
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k58 : x2Key 2 := ⟨58, by decide⟩
x2_gj_cols gj349 349 2 1 6 6 256
theorem gjc58_0 : (List.range 22).all (fun d => gjCheck 256 2 1 6 6 4 11 11 (x2JCols 349 (0 + d)) (gj349.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok58 : ∀ d < x2KeySize 2 k58, gjCheck 256 2 (x2KeyTypes 2 k58 0) (x2KeyTypes 2 k58 1) (x2KeyTypes 2 k58 2) (x2KeyMult 2 k58 0) (x2KeyMult 2 k58 1) (x2KeyMult 2 k58 2) (x2JCols (x2KeyGlobal 2 k58) d) (gj349.getD d 0) = true := by
  have hr : x2KeySize 2 k58 = 22 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 1 6 6 4 11 11 (x2JCols 349 d) (gj349.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 1 6 6 4 11 11 (x2JCols 349 d) (gj349.getD d 0)) 0 22 gjc58_0 d (Nat.zero_le d) (by omega)
x2_v_cols v349 gj349 349 256 484
theorem vc58_0 : (List.range 22).all (fun c => vCheck 256 484 22 gj349 (x2Trial_349.getD (0 + c) 0) (v349.getD (0 + c) 0)) = true := by decide +kernel
theorem vok58 : ∀ c < 22, vCheck 256 (x2KeyMult 2 k58 0 * x2KeyMult 2 k58 1 * x2KeyMult 2 k58 2) (x2KeySize 2 k58) gj349 (x2Trial_349.getD c 0) (v349.getD c 0) = true := by
  intro c hc
  show vCheck 256 484 22 gj349 (x2Trial_349.getD c 0) (v349.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 484 22 gj349 (x2Trial_349.getD c 0) (v349.getD c 0)) 0 22 vc58_0 c (Nat.zero_le c) (by omega)
theorem small58 : x2KeyDegree 2 k58 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k58 0 ∧ 1 ≤ x2KeyMult 2 k58 1 ∧ 1 ≤ x2KeyMult 2 k58 2 ∧ glRowOK 2 (x2KeyTypes 2 k58 0) (x2KeyMult 2 k58 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k58 1) (x2KeyMult 2 k58 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k58 2) (x2KeyMult 2 k58 2) 512 = true ∧ gj349.length = x2KeySize 2 k58 ∧ x2KeySize 2 k58 ≤ 512 ∧ v349.length = 22 := by decide +kernel
theorem chk58 : trialKeyChk 2 k58 22 gj349 x2Trial_349 v349 :=
  trialKeyChk_intro 2 k58 22 gj349 x2Trial_349 v349 small58 gjok58 vok58
def k59 : x2Key 2 := ⟨59, by decide⟩
x2_gj_cols gj350 350 2 1 6 6 256
theorem gjc59_0 : (List.range 18).all (fun d => gjCheck 256 2 1 6 6 4 11 11 (x2JCols 350 (0 + d)) (gj350.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok59 : ∀ d < x2KeySize 2 k59, gjCheck 256 2 (x2KeyTypes 2 k59 0) (x2KeyTypes 2 k59 1) (x2KeyTypes 2 k59 2) (x2KeyMult 2 k59 0) (x2KeyMult 2 k59 1) (x2KeyMult 2 k59 2) (x2JCols (x2KeyGlobal 2 k59) d) (gj350.getD d 0) = true := by
  have hr : x2KeySize 2 k59 = 18 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 1 6 6 4 11 11 (x2JCols 350 d) (gj350.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 1 6 6 4 11 11 (x2JCols 350 d) (gj350.getD d 0)) 0 18 gjc59_0 d (Nat.zero_le d) (by omega)
x2_v_cols v350 gj350 350 256 484
theorem vc59_0 : (List.range 18).all (fun c => vCheck 256 484 18 gj350 (x2Trial_350.getD (0 + c) 0) (v350.getD (0 + c) 0)) = true := by decide +kernel
theorem vok59 : ∀ c < 18, vCheck 256 (x2KeyMult 2 k59 0 * x2KeyMult 2 k59 1 * x2KeyMult 2 k59 2) (x2KeySize 2 k59) gj350 (x2Trial_350.getD c 0) (v350.getD c 0) = true := by
  intro c hc
  show vCheck 256 484 18 gj350 (x2Trial_350.getD c 0) (v350.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 484 18 gj350 (x2Trial_350.getD c 0) (v350.getD c 0)) 0 18 vc59_0 c (Nat.zero_le c) (by omega)
theorem small59 : x2KeyDegree 2 k59 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k59 0 ∧ 1 ≤ x2KeyMult 2 k59 1 ∧ 1 ≤ x2KeyMult 2 k59 2 ∧ glRowOK 2 (x2KeyTypes 2 k59 0) (x2KeyMult 2 k59 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k59 1) (x2KeyMult 2 k59 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k59 2) (x2KeyMult 2 k59 2) 512 = true ∧ gj350.length = x2KeySize 2 k59 ∧ x2KeySize 2 k59 ≤ 512 ∧ v350.length = 18 := by decide +kernel
theorem chk59 : trialKeyChk 2 k59 18 gj350 x2Trial_350 v350 :=
  trialKeyChk_intro 2 k59 18 gj350 x2Trial_350 v350 small59 gjok59 vok59

noncomputable def ks : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := [(k58, ibFS [(v349, v349, 94810963968000)]), (k59, ibFS [(v350, v350, 94810963968000)])]
theorem hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![1, 6, 6] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 2) (hN58 : N k58 = x2TrialForm 2 k58) (hN59 : N k59 = x2TrialForm 2 k59) :
    ∀ e ∈ ks, keyOK (x2Mult 2 1 * x2Mult 2 6 * x2Mult 2 6) 2 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact keyOK_of_trialChk 2 N k58 22 _ gj349 x2Trial_349 v349 (by decide) (by rw [hN58]; exact trialForm_eq 2 k58 22 x2Trial_349 (by decide) rfl) chk58
  · exact keyOK_of_trialChk 2 N k59 18 _ gj350 x2Trial_350 v350 (by decide) (by rw [hN59]; exact trialForm_eq 2 k59 18 x2Trial_350 (by decide) rfl) chk59

end ThreeCopyQutritWerner.X2.InK2x166
