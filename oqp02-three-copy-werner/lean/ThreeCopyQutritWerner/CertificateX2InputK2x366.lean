module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (3, 6, 6) of sector 2, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK2x366
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k99 : x2Key 2 := ⟨99, by decide⟩
x2_gj_cols gj390 390 2 3 6 6 256
theorem gjc99_0 : (List.range 29).all (fun d => gjCheck 256 2 3 6 6 5 11 11 (x2JCols 390 (0 + d)) (gj390.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok99 : ∀ d < x2KeySize 2 k99, gjCheck 256 2 (x2KeyTypes 2 k99 0) (x2KeyTypes 2 k99 1) (x2KeyTypes 2 k99 2) (x2KeyMult 2 k99 0) (x2KeyMult 2 k99 1) (x2KeyMult 2 k99 2) (x2JCols (x2KeyGlobal 2 k99) d) (gj390.getD d 0) = true := by
  have hr : x2KeySize 2 k99 = 29 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 3 6 6 5 11 11 (x2JCols 390 d) (gj390.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 3 6 6 5 11 11 (x2JCols 390 d) (gj390.getD d 0)) 0 29 gjc99_0 d (Nat.zero_le d) (by omega)
x2_v_cols v390 gj390 390 256 605
theorem vc99_0 : (List.range 24).all (fun c => vCheck 256 605 29 gj390 (x2Trial_390.getD (0 + c) 0) (v390.getD (0 + c) 0)) = true := by decide +kernel
theorem vok99 : ∀ c < 24, vCheck 256 (x2KeyMult 2 k99 0 * x2KeyMult 2 k99 1 * x2KeyMult 2 k99 2) (x2KeySize 2 k99) gj390 (x2Trial_390.getD c 0) (v390.getD c 0) = true := by
  intro c hc
  show vCheck 256 605 29 gj390 (x2Trial_390.getD c 0) (v390.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 605 29 gj390 (x2Trial_390.getD c 0) (v390.getD c 0)) 0 24 vc99_0 c (Nat.zero_le c) (by omega)
theorem small99 : x2KeyDegree 2 k99 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k99 0 ∧ 1 ≤ x2KeyMult 2 k99 1 ∧ 1 ≤ x2KeyMult 2 k99 2 ∧ glRowOK 2 (x2KeyTypes 2 k99 0) (x2KeyMult 2 k99 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k99 1) (x2KeyMult 2 k99 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k99 2) (x2KeyMult 2 k99 2) 512 = true ∧ gj390.length = x2KeySize 2 k99 ∧ x2KeySize 2 k99 ≤ 512 ∧ v390.length = 24 := by decide +kernel
theorem chk99 : trialKeyChk 2 k99 24 gj390 x2Trial_390 v390 :=
  trialKeyChk_intro 2 k99 24 gj390 x2Trial_390 v390 small99 gjok99 vok99
def k100 : x2Key 2 := ⟨100, by decide⟩
x2_gj_cols gj391 391 2 3 6 6 256
theorem gjc100_0 : (List.range 22).all (fun d => gjCheck 256 2 3 6 6 5 11 11 (x2JCols 391 (0 + d)) (gj391.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok100 : ∀ d < x2KeySize 2 k100, gjCheck 256 2 (x2KeyTypes 2 k100 0) (x2KeyTypes 2 k100 1) (x2KeyTypes 2 k100 2) (x2KeyMult 2 k100 0) (x2KeyMult 2 k100 1) (x2KeyMult 2 k100 2) (x2JCols (x2KeyGlobal 2 k100) d) (gj391.getD d 0) = true := by
  have hr : x2KeySize 2 k100 = 22 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 3 6 6 5 11 11 (x2JCols 391 d) (gj391.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 3 6 6 5 11 11 (x2JCols 391 d) (gj391.getD d 0)) 0 22 gjc100_0 d (Nat.zero_le d) (by omega)
x2_v_cols v391 gj391 391 256 605
theorem vc100_0 : (List.range 21).all (fun c => vCheck 256 605 22 gj391 (x2Trial_391.getD (0 + c) 0) (v391.getD (0 + c) 0)) = true := by decide +kernel
theorem vok100 : ∀ c < 21, vCheck 256 (x2KeyMult 2 k100 0 * x2KeyMult 2 k100 1 * x2KeyMult 2 k100 2) (x2KeySize 2 k100) gj391 (x2Trial_391.getD c 0) (v391.getD c 0) = true := by
  intro c hc
  show vCheck 256 605 22 gj391 (x2Trial_391.getD c 0) (v391.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 605 22 gj391 (x2Trial_391.getD c 0) (v391.getD c 0)) 0 21 vc100_0 c (Nat.zero_le c) (by omega)
theorem small100 : x2KeyDegree 2 k100 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k100 0 ∧ 1 ≤ x2KeyMult 2 k100 1 ∧ 1 ≤ x2KeyMult 2 k100 2 ∧ glRowOK 2 (x2KeyTypes 2 k100 0) (x2KeyMult 2 k100 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k100 1) (x2KeyMult 2 k100 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k100 2) (x2KeyMult 2 k100 2) 512 = true ∧ gj391.length = x2KeySize 2 k100 ∧ x2KeySize 2 k100 ≤ 512 ∧ v391.length = 21 := by decide +kernel
theorem chk100 : trialKeyChk 2 k100 21 gj391 x2Trial_391 v391 :=
  trialKeyChk_intro 2 k100 21 gj391 x2Trial_391 v391 small100 gjok100 vok100

noncomputable def ks : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := [(k99, ibFS [(v390, v390, 94810963968000)]), (k100, ibFS [(v391, v391, 94810963968000)])]
theorem hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![3, 6, 6] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 2) (hN99 : N k99 = x2TrialForm 2 k99) (hN100 : N k100 = x2TrialForm 2 k100) :
    ∀ e ∈ ks, keyOK (x2Mult 2 3 * x2Mult 2 6 * x2Mult 2 6) 2 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact keyOK_of_trialChk 2 N k99 24 _ gj390 x2Trial_390 v390 (by decide) (by rw [hN99]; exact trialForm_eq 2 k99 24 x2Trial_390 (by decide) rfl) chk99
  · exact keyOK_of_trialChk 2 N k100 21 _ gj391 x2Trial_391 v391 (by decide) (by rw [hN100]; exact trialForm_eq 2 k100 21 x2Trial_391 (by decide) rfl) chk100

end ThreeCopyQutritWerner.X2.InK2x366
