module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (1, 5, 5) of sector 2, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK2x155
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k55 : x2Key 2 := ⟨55, by decide⟩
x2_gj_cols gj346 346 2 1 5 5 256
theorem gjc55_0 : (List.range 18).all (fun d => gjCheck 256 2 1 5 5 4 10 10 (x2JCols 346 (0 + d)) (gj346.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok55 : ∀ d < x2KeySize 2 k55, gjCheck 256 2 (x2KeyTypes 2 k55 0) (x2KeyTypes 2 k55 1) (x2KeyTypes 2 k55 2) (x2KeyMult 2 k55 0) (x2KeyMult 2 k55 1) (x2KeyMult 2 k55 2) (x2JCols (x2KeyGlobal 2 k55) d) (gj346.getD d 0) = true := by
  have hr : x2KeySize 2 k55 = 18 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 1 5 5 4 10 10 (x2JCols 346 d) (gj346.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 1 5 5 4 10 10 (x2JCols 346 d) (gj346.getD d 0)) 0 18 gjc55_0 d (Nat.zero_le d) (by omega)
x2_v_cols v346 gj346 346 256 400
theorem vc55_0 : (List.range 13).all (fun c => vCheck 256 400 18 gj346 (x2Trial_346.getD (0 + c) 0) (v346.getD (0 + c) 0)) = true := by decide +kernel
theorem vok55 : ∀ c < 13, vCheck 256 (x2KeyMult 2 k55 0 * x2KeyMult 2 k55 1 * x2KeyMult 2 k55 2) (x2KeySize 2 k55) gj346 (x2Trial_346.getD c 0) (v346.getD c 0) = true := by
  intro c hc
  show vCheck 256 400 18 gj346 (x2Trial_346.getD c 0) (v346.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 400 18 gj346 (x2Trial_346.getD c 0) (v346.getD c 0)) 0 13 vc55_0 c (Nat.zero_le c) (by omega)
theorem small55 : x2KeyDegree 2 k55 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k55 0 ∧ 1 ≤ x2KeyMult 2 k55 1 ∧ 1 ≤ x2KeyMult 2 k55 2 ∧ glRowOK 2 (x2KeyTypes 2 k55 0) (x2KeyMult 2 k55 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k55 1) (x2KeyMult 2 k55 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k55 2) (x2KeyMult 2 k55 2) 512 = true ∧ gj346.length = x2KeySize 2 k55 ∧ x2KeySize 2 k55 ≤ 512 ∧ v346.length = 13 := by decide +kernel
theorem chk55 : trialKeyChk 2 k55 13 gj346 x2Trial_346 v346 :=
  trialKeyChk_intro 2 k55 13 gj346 x2Trial_346 v346 small55 gjok55 vok55
def k56 : x2Key 2 := ⟨56, by decide⟩
x2_gj_cols gj347 347 2 1 5 5 256
theorem gjc56_0 : (List.range 14).all (fun d => gjCheck 256 2 1 5 5 4 10 10 (x2JCols 347 (0 + d)) (gj347.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok56 : ∀ d < x2KeySize 2 k56, gjCheck 256 2 (x2KeyTypes 2 k56 0) (x2KeyTypes 2 k56 1) (x2KeyTypes 2 k56 2) (x2KeyMult 2 k56 0) (x2KeyMult 2 k56 1) (x2KeyMult 2 k56 2) (x2JCols (x2KeyGlobal 2 k56) d) (gj347.getD d 0) = true := by
  have hr : x2KeySize 2 k56 = 14 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 1 5 5 4 10 10 (x2JCols 347 d) (gj347.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 1 5 5 4 10 10 (x2JCols 347 d) (gj347.getD d 0)) 0 14 gjc56_0 d (Nat.zero_le d) (by omega)
x2_v_cols v347 gj347 347 256 400
theorem vc56_0 : (List.range 11).all (fun c => vCheck 256 400 14 gj347 (x2Trial_347.getD (0 + c) 0) (v347.getD (0 + c) 0)) = true := by decide +kernel
theorem vok56 : ∀ c < 11, vCheck 256 (x2KeyMult 2 k56 0 * x2KeyMult 2 k56 1 * x2KeyMult 2 k56 2) (x2KeySize 2 k56) gj347 (x2Trial_347.getD c 0) (v347.getD c 0) = true := by
  intro c hc
  show vCheck 256 400 14 gj347 (x2Trial_347.getD c 0) (v347.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 400 14 gj347 (x2Trial_347.getD c 0) (v347.getD c 0)) 0 11 vc56_0 c (Nat.zero_le c) (by omega)
theorem small56 : x2KeyDegree 2 k56 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k56 0 ∧ 1 ≤ x2KeyMult 2 k56 1 ∧ 1 ≤ x2KeyMult 2 k56 2 ∧ glRowOK 2 (x2KeyTypes 2 k56 0) (x2KeyMult 2 k56 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k56 1) (x2KeyMult 2 k56 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k56 2) (x2KeyMult 2 k56 2) 512 = true ∧ gj347.length = x2KeySize 2 k56 ∧ x2KeySize 2 k56 ≤ 512 ∧ v347.length = 11 := by decide +kernel
theorem chk56 : trialKeyChk 2 k56 11 gj347 x2Trial_347 v347 :=
  trialKeyChk_intro 2 k56 11 gj347 x2Trial_347 v347 small56 gjok56 vok56

noncomputable def ks : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := [(k55, ibFS [(v346, v346, 94810963968000)]), (k56, ibFS [(v347, v347, 94810963968000)])]
theorem hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![1, 5, 5] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 2) (hN55 : N k55 = x2TrialForm 2 k55) (hN56 : N k56 = x2TrialForm 2 k56) :
    ∀ e ∈ ks, keyOK (x2Mult 2 1 * x2Mult 2 5 * x2Mult 2 5) 2 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact keyOK_of_trialChk 2 N k55 13 _ gj346 x2Trial_346 v346 (by decide) (by rw [hN55]; exact trialForm_eq 2 k55 13 x2Trial_346 (by decide) rfl) chk55
  · exact keyOK_of_trialChk 2 N k56 11 _ gj347 x2Trial_347 v347 (by decide) (by rw [hN56]; exact trialForm_eq 2 k56 11 x2Trial_347 (by decide) rfl) chk56

end ThreeCopyQutritWerner.X2.InK2x155
