module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (3, 3, 4) of sector 2, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK2x334
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k86 : x2Key 2 := ⟨86, by decide⟩
x2_gj_cols gj377 377 2 3 3 4 256
theorem gjc86_0 : (List.range 18).all (fun d => gjCheck 256 2 3 3 4 5 5 15 (x2JCols 377 (0 + d)) (gj377.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok86 : ∀ d < x2KeySize 2 k86, gjCheck 256 2 (x2KeyTypes 2 k86 0) (x2KeyTypes 2 k86 1) (x2KeyTypes 2 k86 2) (x2KeyMult 2 k86 0) (x2KeyMult 2 k86 1) (x2KeyMult 2 k86 2) (x2JCols (x2KeyGlobal 2 k86) d) (gj377.getD d 0) = true := by
  have hr : x2KeySize 2 k86 = 18 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 3 3 4 5 5 15 (x2JCols 377 d) (gj377.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 3 3 4 5 5 15 (x2JCols 377 d) (gj377.getD d 0)) 0 18 gjc86_0 d (Nat.zero_le d) (by omega)
x2_v_cols v377 gj377 377 256 375
theorem vc86_0 : (List.range 5).all (fun c => vCheck 256 375 18 gj377 (x2Trial_377.getD (0 + c) 0) (v377.getD (0 + c) 0)) = true := by decide +kernel
theorem vok86 : ∀ c < 5, vCheck 256 (x2KeyMult 2 k86 0 * x2KeyMult 2 k86 1 * x2KeyMult 2 k86 2) (x2KeySize 2 k86) gj377 (x2Trial_377.getD c 0) (v377.getD c 0) = true := by
  intro c hc
  show vCheck 256 375 18 gj377 (x2Trial_377.getD c 0) (v377.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 375 18 gj377 (x2Trial_377.getD c 0) (v377.getD c 0)) 0 5 vc86_0 c (Nat.zero_le c) (by omega)
theorem small86 : x2KeyDegree 2 k86 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k86 0 ∧ 1 ≤ x2KeyMult 2 k86 1 ∧ 1 ≤ x2KeyMult 2 k86 2 ∧ glRowOK 2 (x2KeyTypes 2 k86 0) (x2KeyMult 2 k86 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k86 1) (x2KeyMult 2 k86 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k86 2) (x2KeyMult 2 k86 2) 512 = true ∧ gj377.length = x2KeySize 2 k86 ∧ x2KeySize 2 k86 ≤ 512 ∧ v377.length = 5 := by decide +kernel
theorem chk86 : trialKeyChk 2 k86 5 gj377 x2Trial_377 v377 :=
  trialKeyChk_intro 2 k86 5 gj377 x2Trial_377 v377 small86 gjok86 vok86
def k87 : x2Key 2 := ⟨87, by decide⟩
x2_gj_cols gj378 378 2 3 3 4 256
theorem gjc87_0 : (List.range 13).all (fun d => gjCheck 256 2 3 3 4 5 5 15 (x2JCols 378 (0 + d)) (gj378.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok87 : ∀ d < x2KeySize 2 k87, gjCheck 256 2 (x2KeyTypes 2 k87 0) (x2KeyTypes 2 k87 1) (x2KeyTypes 2 k87 2) (x2KeyMult 2 k87 0) (x2KeyMult 2 k87 1) (x2KeyMult 2 k87 2) (x2JCols (x2KeyGlobal 2 k87) d) (gj378.getD d 0) = true := by
  have hr : x2KeySize 2 k87 = 13 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 3 3 4 5 5 15 (x2JCols 378 d) (gj378.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 3 3 4 5 5 15 (x2JCols 378 d) (gj378.getD d 0)) 0 13 gjc87_0 d (Nat.zero_le d) (by omega)
x2_v_cols v378 gj378 378 256 375
theorem vc87_0 : (List.range 5).all (fun c => vCheck 256 375 13 gj378 (x2Trial_378.getD (0 + c) 0) (v378.getD (0 + c) 0)) = true := by decide +kernel
theorem vok87 : ∀ c < 5, vCheck 256 (x2KeyMult 2 k87 0 * x2KeyMult 2 k87 1 * x2KeyMult 2 k87 2) (x2KeySize 2 k87) gj378 (x2Trial_378.getD c 0) (v378.getD c 0) = true := by
  intro c hc
  show vCheck 256 375 13 gj378 (x2Trial_378.getD c 0) (v378.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 375 13 gj378 (x2Trial_378.getD c 0) (v378.getD c 0)) 0 5 vc87_0 c (Nat.zero_le c) (by omega)
theorem small87 : x2KeyDegree 2 k87 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k87 0 ∧ 1 ≤ x2KeyMult 2 k87 1 ∧ 1 ≤ x2KeyMult 2 k87 2 ∧ glRowOK 2 (x2KeyTypes 2 k87 0) (x2KeyMult 2 k87 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k87 1) (x2KeyMult 2 k87 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k87 2) (x2KeyMult 2 k87 2) 512 = true ∧ gj378.length = x2KeySize 2 k87 ∧ x2KeySize 2 k87 ≤ 512 ∧ v378.length = 5 := by decide +kernel
theorem chk87 : trialKeyChk 2 k87 5 gj378 x2Trial_378 v378 :=
  trialKeyChk_intro 2 k87 5 gj378 x2Trial_378 v378 small87 gjok87 vok87

noncomputable def ks : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := [(k86, ibFS [(v377, v377, 94810963968000)]), (k87, ibFS [(v378, v378, 94810963968000)])]
theorem hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![3, 3, 4] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 2) (hN86 : N k86 = x2TrialForm 2 k86) (hN87 : N k87 = x2TrialForm 2 k87) :
    ∀ e ∈ ks, keyOK (x2Mult 2 3 * x2Mult 2 3 * x2Mult 2 4) 2 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact keyOK_of_trialChk 2 N k86 5 _ gj377 x2Trial_377 v377 (by decide) (by rw [hN86]; exact trialForm_eq 2 k86 5 x2Trial_377 (by decide) rfl) chk86
  · exact keyOK_of_trialChk 2 N k87 5 _ gj378 x2Trial_378 v378 (by decide) (by rw [hN87]; exact trialForm_eq 2 k87 5 x2Trial_378 (by decide) rfl) chk87

end ThreeCopyQutritWerner.X2.InK2x334
