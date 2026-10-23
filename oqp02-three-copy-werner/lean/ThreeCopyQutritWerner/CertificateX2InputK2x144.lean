module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (1, 4, 4) of sector 2, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK2x144
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k51 : x2Key 2 := ⟨51, by decide⟩
x2_gj_cols gj342 342 2 1 4 4 256
theorem gjc51_0 : (List.range 40).all (fun d => gjCheck 256 2 1 4 4 4 15 15 (x2JCols 342 (0 + d)) (gj342.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok51 : ∀ d < x2KeySize 2 k51, gjCheck 256 2 (x2KeyTypes 2 k51 0) (x2KeyTypes 2 k51 1) (x2KeyTypes 2 k51 2) (x2KeyMult 2 k51 0) (x2KeyMult 2 k51 1) (x2KeyMult 2 k51 2) (x2JCols (x2KeyGlobal 2 k51) d) (gj342.getD d 0) = true := by
  have hr : x2KeySize 2 k51 = 40 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 1 4 4 4 15 15 (x2JCols 342 d) (gj342.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 1 4 4 4 15 15 (x2JCols 342 d) (gj342.getD d 0)) 0 40 gjc51_0 d (Nat.zero_le d) (by omega)
x2_v_cols v342 gj342 342 256 900
theorem vc51_0 : (List.range 25).all (fun c => vCheck 256 900 40 gj342 (x2Trial_342.getD (0 + c) 0) (v342.getD (0 + c) 0)) = true := by decide +kernel
theorem vok51 : ∀ c < 25, vCheck 256 (x2KeyMult 2 k51 0 * x2KeyMult 2 k51 1 * x2KeyMult 2 k51 2) (x2KeySize 2 k51) gj342 (x2Trial_342.getD c 0) (v342.getD c 0) = true := by
  intro c hc
  show vCheck 256 900 40 gj342 (x2Trial_342.getD c 0) (v342.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 900 40 gj342 (x2Trial_342.getD c 0) (v342.getD c 0)) 0 25 vc51_0 c (Nat.zero_le c) (by omega)
theorem small51 : x2KeyDegree 2 k51 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k51 0 ∧ 1 ≤ x2KeyMult 2 k51 1 ∧ 1 ≤ x2KeyMult 2 k51 2 ∧ glRowOK 2 (x2KeyTypes 2 k51 0) (x2KeyMult 2 k51 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k51 1) (x2KeyMult 2 k51 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k51 2) (x2KeyMult 2 k51 2) 512 = true ∧ gj342.length = x2KeySize 2 k51 ∧ x2KeySize 2 k51 ≤ 512 ∧ v342.length = 25 := by decide +kernel
theorem chk51 : trialKeyChk 2 k51 25 gj342 x2Trial_342 v342 :=
  trialKeyChk_intro 2 k51 25 gj342 x2Trial_342 v342 small51 gjok51 vok51
def k52 : x2Key 2 := ⟨52, by decide⟩
x2_gj_cols gj343 343 2 1 4 4 256
theorem gjc52_0 : (List.range 35).all (fun d => gjCheck 256 2 1 4 4 4 15 15 (x2JCols 343 (0 + d)) (gj343.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok52 : ∀ d < x2KeySize 2 k52, gjCheck 256 2 (x2KeyTypes 2 k52 0) (x2KeyTypes 2 k52 1) (x2KeyTypes 2 k52 2) (x2KeyMult 2 k52 0) (x2KeyMult 2 k52 1) (x2KeyMult 2 k52 2) (x2JCols (x2KeyGlobal 2 k52) d) (gj343.getD d 0) = true := by
  have hr : x2KeySize 2 k52 = 35 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 1 4 4 4 15 15 (x2JCols 343 d) (gj343.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 1 4 4 4 15 15 (x2JCols 343 d) (gj343.getD d 0)) 0 35 gjc52_0 d (Nat.zero_le d) (by omega)
x2_v_cols v343 gj343 343 256 900
theorem vc52_0 : (List.range 23).all (fun c => vCheck 256 900 35 gj343 (x2Trial_343.getD (0 + c) 0) (v343.getD (0 + c) 0)) = true := by decide +kernel
theorem vok52 : ∀ c < 23, vCheck 256 (x2KeyMult 2 k52 0 * x2KeyMult 2 k52 1 * x2KeyMult 2 k52 2) (x2KeySize 2 k52) gj343 (x2Trial_343.getD c 0) (v343.getD c 0) = true := by
  intro c hc
  show vCheck 256 900 35 gj343 (x2Trial_343.getD c 0) (v343.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 900 35 gj343 (x2Trial_343.getD c 0) (v343.getD c 0)) 0 23 vc52_0 c (Nat.zero_le c) (by omega)
theorem small52 : x2KeyDegree 2 k52 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k52 0 ∧ 1 ≤ x2KeyMult 2 k52 1 ∧ 1 ≤ x2KeyMult 2 k52 2 ∧ glRowOK 2 (x2KeyTypes 2 k52 0) (x2KeyMult 2 k52 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k52 1) (x2KeyMult 2 k52 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k52 2) (x2KeyMult 2 k52 2) 512 = true ∧ gj343.length = x2KeySize 2 k52 ∧ x2KeySize 2 k52 ≤ 512 ∧ v343.length = 23 := by decide +kernel
theorem chk52 : trialKeyChk 2 k52 23 gj343 x2Trial_343 v343 :=
  trialKeyChk_intro 2 k52 23 gj343 x2Trial_343 v343 small52 gjok52 vok52

noncomputable def ks : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := [(k51, ibFS [(v342, v342, 94810963968000)]), (k52, ibFS [(v343, v343, 94810963968000)])]
theorem hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![1, 4, 4] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 2) (hN51 : N k51 = x2TrialForm 2 k51) (hN52 : N k52 = x2TrialForm 2 k52) :
    ∀ e ∈ ks, keyOK (x2Mult 2 1 * x2Mult 2 4 * x2Mult 2 4) 2 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact keyOK_of_trialChk 2 N k51 25 _ gj342 x2Trial_342 v342 (by decide) (by rw [hN51]; exact trialForm_eq 2 k51 25 x2Trial_342 (by decide) rfl) chk51
  · exact keyOK_of_trialChk 2 N k52 23 _ gj343 x2Trial_343 v343 (by decide) (by rw [hN52]; exact trialForm_eq 2 k52 23 x2Trial_343 (by decide) rfl) chk52

end ThreeCopyQutritWerner.X2.InK2x144
