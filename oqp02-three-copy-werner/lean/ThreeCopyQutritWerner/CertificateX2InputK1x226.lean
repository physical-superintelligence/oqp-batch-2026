module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (2, 2, 6) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x226
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k80 : x2Key 1 := ⟨80, by decide⟩
x2_gj_cols gj202 202 1 2 2 6 256
theorem gjc80_0 : (List.range 8).all (fun d => gjCheck 256 1 2 2 6 2 2 17 (x2JCols 202 (0 + d)) (gj202.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok80 : ∀ d < x2KeySize 1 k80, gjCheck 256 1 (x2KeyTypes 1 k80 0) (x2KeyTypes 1 k80 1) (x2KeyTypes 1 k80 2) (x2KeyMult 1 k80 0) (x2KeyMult 1 k80 1) (x2KeyMult 1 k80 2) (x2JCols (x2KeyGlobal 1 k80) d) (gj202.getD d 0) = true := by
  have hr : x2KeySize 1 k80 = 8 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 2 2 6 2 2 17 (x2JCols 202 d) (gj202.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 2 2 6 2 2 17 (x2JCols 202 d) (gj202.getD d 0)) 0 8 gjc80_0 d (Nat.zero_le d) (by omega)
x2_v_cols v202 gj202 202 256 68
theorem vc80_0 : (List.range 3).all (fun c => vCheck 256 68 8 gj202 (x2Trial_202.getD (0 + c) 0) (v202.getD (0 + c) 0)) = true := by decide +kernel
theorem vok80 : ∀ c < 3, vCheck 256 (x2KeyMult 1 k80 0 * x2KeyMult 1 k80 1 * x2KeyMult 1 k80 2) (x2KeySize 1 k80) gj202 (x2Trial_202.getD c 0) (v202.getD c 0) = true := by
  intro c hc
  show vCheck 256 68 8 gj202 (x2Trial_202.getD c 0) (v202.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 68 8 gj202 (x2Trial_202.getD c 0) (v202.getD c 0)) 0 3 vc80_0 c (Nat.zero_le c) (by omega)
theorem small80 : x2KeyDegree 1 k80 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k80 0 ∧ 1 ≤ x2KeyMult 1 k80 1 ∧ 1 ≤ x2KeyMult 1 k80 2 ∧ glRowOK 1 (x2KeyTypes 1 k80 0) (x2KeyMult 1 k80 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k80 1) (x2KeyMult 1 k80 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k80 2) (x2KeyMult 1 k80 2) 512 = true ∧ gj202.length = x2KeySize 1 k80 ∧ x2KeySize 1 k80 ≤ 512 ∧ v202.length = 3 := by decide +kernel
theorem chk80 : trialKeyChk 1 k80 3 gj202 x2Trial_202 v202 :=
  trialKeyChk_intro 1 k80 3 gj202 x2Trial_202 v202 small80 gjok80 vok80
def k81 : x2Key 1 := ⟨81, by decide⟩
x2_gj_cols gj203 203 1 2 2 6 256
theorem gjc81_0 : (List.range 3).all (fun d => gjCheck 256 1 2 2 6 2 2 17 (x2JCols 203 (0 + d)) (gj203.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok81 : ∀ d < x2KeySize 1 k81, gjCheck 256 1 (x2KeyTypes 1 k81 0) (x2KeyTypes 1 k81 1) (x2KeyTypes 1 k81 2) (x2KeyMult 1 k81 0) (x2KeyMult 1 k81 1) (x2KeyMult 1 k81 2) (x2JCols (x2KeyGlobal 1 k81) d) (gj203.getD d 0) = true := by
  have hr : x2KeySize 1 k81 = 3 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 2 2 6 2 2 17 (x2JCols 203 d) (gj203.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 2 2 6 2 2 17 (x2JCols 203 d) (gj203.getD d 0)) 0 3 gjc81_0 d (Nat.zero_le d) (by omega)
x2_v_cols v203 gj203 203 256 68
theorem vc81_0 : (List.range 1).all (fun c => vCheck 256 68 3 gj203 (x2Trial_203.getD (0 + c) 0) (v203.getD (0 + c) 0)) = true := by decide +kernel
theorem vok81 : ∀ c < 1, vCheck 256 (x2KeyMult 1 k81 0 * x2KeyMult 1 k81 1 * x2KeyMult 1 k81 2) (x2KeySize 1 k81) gj203 (x2Trial_203.getD c 0) (v203.getD c 0) = true := by
  intro c hc
  show vCheck 256 68 3 gj203 (x2Trial_203.getD c 0) (v203.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 68 3 gj203 (x2Trial_203.getD c 0) (v203.getD c 0)) 0 1 vc81_0 c (Nat.zero_le c) (by omega)
theorem small81 : x2KeyDegree 1 k81 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k81 0 ∧ 1 ≤ x2KeyMult 1 k81 1 ∧ 1 ≤ x2KeyMult 1 k81 2 ∧ glRowOK 1 (x2KeyTypes 1 k81 0) (x2KeyMult 1 k81 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k81 1) (x2KeyMult 1 k81 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k81 2) (x2KeyMult 1 k81 2) 512 = true ∧ gj203.length = x2KeySize 1 k81 ∧ x2KeySize 1 k81 ≤ 512 ∧ v203.length = 1 := by decide +kernel
theorem chk81 : trialKeyChk 1 k81 1 gj203 x2Trial_203 v203 :=
  trialKeyChk_intro 1 k81 1 gj203 x2Trial_203 v203 small81 gjok81 vok81

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k80, ibFS [(v202, v202, 94810963968000)]), (k81, ibFS [(v203, v203, 94810963968000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![2, 2, 6] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN80 : N k80 = x2TrialForm 1 k80) (hN81 : N k81 = x2TrialForm 1 k81) :
    ∀ e ∈ ks, keyOK (x2Mult 1 2 * x2Mult 1 2 * x2Mult 1 6) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact keyOK_of_trialChk 1 N k80 3 _ gj202 x2Trial_202 v202 (by decide) (by rw [hN80]; exact trialForm_eq 1 k80 3 x2Trial_202 (by decide) rfl) chk80
  · exact keyOK_of_trialChk 1 N k81 1 _ gj203 x2Trial_203 v203 (by decide) (by rw [hN81]; exact trialForm_eq 1 k81 1 x2Trial_203 (by decide) rfl) chk81

end ThreeCopyQutritWerner.X2.InK1x226
