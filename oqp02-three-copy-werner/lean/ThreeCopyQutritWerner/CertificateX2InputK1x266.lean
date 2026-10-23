module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (2, 6, 6) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x266
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k99 : x2Key 1 := ⟨99, by decide⟩
x2_gj_cols gj221 221 1 2 6 6 256
theorem gjc99_0 : (List.range 48).all (fun d => gjCheck 256 1 2 6 6 2 17 17 (x2JCols 221 (0 + d)) (gj221.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok99 : ∀ d < x2KeySize 1 k99, gjCheck 256 1 (x2KeyTypes 1 k99 0) (x2KeyTypes 1 k99 1) (x2KeyTypes 1 k99 2) (x2KeyMult 1 k99 0) (x2KeyMult 1 k99 1) (x2KeyMult 1 k99 2) (x2JCols (x2KeyGlobal 1 k99) d) (gj221.getD d 0) = true := by
  have hr : x2KeySize 1 k99 = 48 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 2 6 6 2 17 17 (x2JCols 221 d) (gj221.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 2 6 6 2 17 17 (x2JCols 221 d) (gj221.getD d 0)) 0 48 gjc99_0 d (Nat.zero_le d) (by omega)
x2_v_cols v221 gj221 221 256 578
theorem vc99_0 : (List.range 27).all (fun c => vCheck 256 578 48 gj221 (x2Trial_221.getD (0 + c) 0) (v221.getD (0 + c) 0)) = true := by decide +kernel
theorem vok99 : ∀ c < 27, vCheck 256 (x2KeyMult 1 k99 0 * x2KeyMult 1 k99 1 * x2KeyMult 1 k99 2) (x2KeySize 1 k99) gj221 (x2Trial_221.getD c 0) (v221.getD c 0) = true := by
  intro c hc
  show vCheck 256 578 48 gj221 (x2Trial_221.getD c 0) (v221.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 578 48 gj221 (x2Trial_221.getD c 0) (v221.getD c 0)) 0 27 vc99_0 c (Nat.zero_le c) (by omega)
theorem small99 : x2KeyDegree 1 k99 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k99 0 ∧ 1 ≤ x2KeyMult 1 k99 1 ∧ 1 ≤ x2KeyMult 1 k99 2 ∧ glRowOK 1 (x2KeyTypes 1 k99 0) (x2KeyMult 1 k99 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k99 1) (x2KeyMult 1 k99 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k99 2) (x2KeyMult 1 k99 2) 512 = true ∧ gj221.length = x2KeySize 1 k99 ∧ x2KeySize 1 k99 ≤ 512 ∧ v221.length = 27 := by decide +kernel
theorem chk99 : trialKeyChk 1 k99 27 gj221 x2Trial_221 v221 :=
  trialKeyChk_intro 1 k99 27 gj221 x2Trial_221 v221 small99 gjok99 vok99
def k100 : x2Key 1 := ⟨100, by decide⟩
x2_gj_cols gj222 222 1 2 6 6 256
theorem gjc100_0 : (List.range 48).all (fun d => gjCheck 256 1 2 6 6 2 17 17 (x2JCols 222 (0 + d)) (gj222.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok100 : ∀ d < x2KeySize 1 k100, gjCheck 256 1 (x2KeyTypes 1 k100 0) (x2KeyTypes 1 k100 1) (x2KeyTypes 1 k100 2) (x2KeyMult 1 k100 0) (x2KeyMult 1 k100 1) (x2KeyMult 1 k100 2) (x2JCols (x2KeyGlobal 1 k100) d) (gj222.getD d 0) = true := by
  have hr : x2KeySize 1 k100 = 48 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 2 6 6 2 17 17 (x2JCols 222 d) (gj222.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 2 6 6 2 17 17 (x2JCols 222 d) (gj222.getD d 0)) 0 48 gjc100_0 d (Nat.zero_le d) (by omega)
x2_v_cols v222 gj222 222 256 578
theorem vc100_0 : (List.range 27).all (fun c => vCheck 256 578 48 gj222 (x2Trial_222.getD (0 + c) 0) (v222.getD (0 + c) 0)) = true := by decide +kernel
theorem vok100 : ∀ c < 27, vCheck 256 (x2KeyMult 1 k100 0 * x2KeyMult 1 k100 1 * x2KeyMult 1 k100 2) (x2KeySize 1 k100) gj222 (x2Trial_222.getD c 0) (v222.getD c 0) = true := by
  intro c hc
  show vCheck 256 578 48 gj222 (x2Trial_222.getD c 0) (v222.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 578 48 gj222 (x2Trial_222.getD c 0) (v222.getD c 0)) 0 27 vc100_0 c (Nat.zero_le c) (by omega)
theorem small100 : x2KeyDegree 1 k100 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k100 0 ∧ 1 ≤ x2KeyMult 1 k100 1 ∧ 1 ≤ x2KeyMult 1 k100 2 ∧ glRowOK 1 (x2KeyTypes 1 k100 0) (x2KeyMult 1 k100 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k100 1) (x2KeyMult 1 k100 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k100 2) (x2KeyMult 1 k100 2) 512 = true ∧ gj222.length = x2KeySize 1 k100 ∧ x2KeySize 1 k100 ≤ 512 ∧ v222.length = 27 := by decide +kernel
theorem chk100 : trialKeyChk 1 k100 27 gj222 x2Trial_222 v222 :=
  trialKeyChk_intro 1 k100 27 gj222 x2Trial_222 v222 small100 gjok100 vok100

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k99, ibFS [(v221, v221, 94810963968000)]), (k100, ibFS [(v222, v222, 94810963968000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![2, 6, 6] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN99 : N k99 = x2TrialForm 1 k99) (hN100 : N k100 = x2TrialForm 1 k100) :
    ∀ e ∈ ks, keyOK (x2Mult 1 2 * x2Mult 1 6 * x2Mult 1 6) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact keyOK_of_trialChk 1 N k99 27 _ gj221 x2Trial_221 v221 (by decide) (by rw [hN99]; exact trialForm_eq 1 k99 27 x2Trial_221 (by decide) rfl) chk99
  · exact keyOK_of_trialChk 1 N k100 27 _ gj222 x2Trial_222 v222 (by decide) (by rw [hN100]; exact trialForm_eq 1 k100 27 x2Trial_222 (by decide) rfl) chk100

end ThreeCopyQutritWerner.X2.InK1x266
