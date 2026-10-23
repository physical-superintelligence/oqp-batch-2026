module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (4, 4, 6) of sector 2, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK2x446
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k106 : x2Key 2 := ⟨106, by decide⟩
x2_gj_cols gj397 397 2 4 4 6 256
theorem gjc106_0 : (List.range 108).all (fun d => gjCheck 256 2 4 4 6 15 15 11 (x2JCols 397 (0 + d)) (gj397.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok106 : ∀ d < x2KeySize 2 k106, gjCheck 256 2 (x2KeyTypes 2 k106 0) (x2KeyTypes 2 k106 1) (x2KeyTypes 2 k106 2) (x2KeyMult 2 k106 0) (x2KeyMult 2 k106 1) (x2KeyMult 2 k106 2) (x2JCols (x2KeyGlobal 2 k106) d) (gj397.getD d 0) = true := by
  have hr : x2KeySize 2 k106 = 108 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 4 4 6 15 15 11 (x2JCols 397 d) (gj397.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 4 4 6 15 15 11 (x2JCols 397 d) (gj397.getD d 0)) 0 108 gjc106_0 d (Nat.zero_le d) (by omega)
x2_v_cols v397 gj397 397 256 2475
theorem vc106_0 : (List.range 108).all (fun c => vCheck 256 2475 108 gj397 (x2Trial_397.getD (0 + c) 0) (v397.getD (0 + c) 0)) = true := by decide +kernel
theorem vok106 : ∀ c < 108, vCheck 256 (x2KeyMult 2 k106 0 * x2KeyMult 2 k106 1 * x2KeyMult 2 k106 2) (x2KeySize 2 k106) gj397 (x2Trial_397.getD c 0) (v397.getD c 0) = true := by
  intro c hc
  show vCheck 256 2475 108 gj397 (x2Trial_397.getD c 0) (v397.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 2475 108 gj397 (x2Trial_397.getD c 0) (v397.getD c 0)) 0 108 vc106_0 c (Nat.zero_le c) (by omega)
theorem small106 : x2KeyDegree 2 k106 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k106 0 ∧ 1 ≤ x2KeyMult 2 k106 1 ∧ 1 ≤ x2KeyMult 2 k106 2 ∧ glRowOK 2 (x2KeyTypes 2 k106 0) (x2KeyMult 2 k106 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k106 1) (x2KeyMult 2 k106 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k106 2) (x2KeyMult 2 k106 2) 512 = true ∧ gj397.length = x2KeySize 2 k106 ∧ x2KeySize 2 k106 ≤ 512 ∧ v397.length = 108 := by decide +kernel
theorem chk106 : trialKeyChk 2 k106 108 gj397 x2Trial_397 v397 :=
  trialKeyChk_intro 2 k106 108 gj397 x2Trial_397 v397 small106 gjok106 vok106
def k107 : x2Key 2 := ⟨107, by decide⟩
x2_gj_cols gj398 398 2 4 4 6 256
theorem gjc107_0 : (List.range 98).all (fun d => gjCheck 256 2 4 4 6 15 15 11 (x2JCols 398 (0 + d)) (gj398.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok107 : ∀ d < x2KeySize 2 k107, gjCheck 256 2 (x2KeyTypes 2 k107 0) (x2KeyTypes 2 k107 1) (x2KeyTypes 2 k107 2) (x2KeyMult 2 k107 0) (x2KeyMult 2 k107 1) (x2KeyMult 2 k107 2) (x2JCols (x2KeyGlobal 2 k107) d) (gj398.getD d 0) = true := by
  have hr : x2KeySize 2 k107 = 98 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 4 4 6 15 15 11 (x2JCols 398 d) (gj398.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 4 4 6 15 15 11 (x2JCols 398 d) (gj398.getD d 0)) 0 98 gjc107_0 d (Nat.zero_le d) (by omega)
x2_v_cols v398 gj398 398 256 2475
theorem vc107_0 : (List.range 98).all (fun c => vCheck 256 2475 98 gj398 (x2Trial_398.getD (0 + c) 0) (v398.getD (0 + c) 0)) = true := by decide +kernel
theorem vok107 : ∀ c < 98, vCheck 256 (x2KeyMult 2 k107 0 * x2KeyMult 2 k107 1 * x2KeyMult 2 k107 2) (x2KeySize 2 k107) gj398 (x2Trial_398.getD c 0) (v398.getD c 0) = true := by
  intro c hc
  show vCheck 256 2475 98 gj398 (x2Trial_398.getD c 0) (v398.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 2475 98 gj398 (x2Trial_398.getD c 0) (v398.getD c 0)) 0 98 vc107_0 c (Nat.zero_le c) (by omega)
theorem small107 : x2KeyDegree 2 k107 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k107 0 ∧ 1 ≤ x2KeyMult 2 k107 1 ∧ 1 ≤ x2KeyMult 2 k107 2 ∧ glRowOK 2 (x2KeyTypes 2 k107 0) (x2KeyMult 2 k107 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k107 1) (x2KeyMult 2 k107 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k107 2) (x2KeyMult 2 k107 2) 512 = true ∧ gj398.length = x2KeySize 2 k107 ∧ x2KeySize 2 k107 ≤ 512 ∧ v398.length = 98 := by decide +kernel
theorem chk107 : trialKeyChk 2 k107 98 gj398 x2Trial_398 v398 :=
  trialKeyChk_intro 2 k107 98 gj398 x2Trial_398 v398 small107 gjok107 vok107

noncomputable def ks : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := [(k106, ibFS [(v397, v397, 94810963968000)]), (k107, ibFS [(v398, v398, 94810963968000)])]
theorem hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![4, 4, 6] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 2) (hN106 : N k106 = x2TrialForm 2 k106) (hN107 : N k107 = x2TrialForm 2 k107) :
    ∀ e ∈ ks, keyOK (x2Mult 2 4 * x2Mult 2 4 * x2Mult 2 6) 2 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact keyOK_of_trialChk 2 N k106 108 _ gj397 x2Trial_397 v397 (by decide) (by rw [hN106]; exact trialForm_eq 2 k106 108 x2Trial_397 (by decide) rfl) chk106
  · exact keyOK_of_trialChk 2 N k107 98 _ gj398 x2Trial_398 v398 (by decide) (by rw [hN107]; exact trialForm_eq 2 k107 98 x2Trial_398 (by decide) rfl) chk107

end ThreeCopyQutritWerner.X2.InK2x446
