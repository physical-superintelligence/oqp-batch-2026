module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (2, 3, 7) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x237
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k89 : x2Key 1 := ⟨89, by decide⟩
x2_gj_cols gj211 211 1 2 3 7 256
theorem gjc89_0 : (List.range 18).all (fun d => gjCheck 256 1 2 3 7 2 9 6 (x2JCols 211 (0 + d)) (gj211.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok89 : ∀ d < x2KeySize 1 k89, gjCheck 256 1 (x2KeyTypes 1 k89 0) (x2KeyTypes 1 k89 1) (x2KeyTypes 1 k89 2) (x2KeyMult 1 k89 0) (x2KeyMult 1 k89 1) (x2KeyMult 1 k89 2) (x2JCols (x2KeyGlobal 1 k89) d) (gj211.getD d 0) = true := by
  have hr : x2KeySize 1 k89 = 18 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 2 3 7 2 9 6 (x2JCols 211 d) (gj211.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 2 3 7 2 9 6 (x2JCols 211 d) (gj211.getD d 0)) 0 18 gjc89_0 d (Nat.zero_le d) (by omega)
x2_v_cols v211 gj211 211 256 108
theorem vc89_0 : (List.range 5).all (fun c => vCheck 256 108 18 gj211 (x2Trial_211.getD (0 + c) 0) (v211.getD (0 + c) 0)) = true := by decide +kernel
theorem vok89 : ∀ c < 5, vCheck 256 (x2KeyMult 1 k89 0 * x2KeyMult 1 k89 1 * x2KeyMult 1 k89 2) (x2KeySize 1 k89) gj211 (x2Trial_211.getD c 0) (v211.getD c 0) = true := by
  intro c hc
  show vCheck 256 108 18 gj211 (x2Trial_211.getD c 0) (v211.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 108 18 gj211 (x2Trial_211.getD c 0) (v211.getD c 0)) 0 5 vc89_0 c (Nat.zero_le c) (by omega)
theorem small89 : x2KeyDegree 1 k89 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k89 0 ∧ 1 ≤ x2KeyMult 1 k89 1 ∧ 1 ≤ x2KeyMult 1 k89 2 ∧ glRowOK 1 (x2KeyTypes 1 k89 0) (x2KeyMult 1 k89 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k89 1) (x2KeyMult 1 k89 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k89 2) (x2KeyMult 1 k89 2) 512 = true ∧ gj211.length = x2KeySize 1 k89 ∧ x2KeySize 1 k89 ≤ 512 ∧ v211.length = 5 := by decide +kernel
theorem chk89 : trialKeyChk 1 k89 5 gj211 x2Trial_211 v211 :=
  trialKeyChk_intro 1 k89 5 gj211 x2Trial_211 v211 small89 gjok89 vok89

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k89, ibFS [(v211, v211, 94810963968000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![2, 3, 7] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN89 : N k89 = x2TrialForm 1 k89) :
    ∀ e ∈ ks, keyOK (x2Mult 1 2 * x2Mult 1 3 * x2Mult 1 7) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_singleton] at he
  subst he
  exact keyOK_of_trialChk 1 N k89 5 _ gj211 x2Trial_211 v211 (by decide) (by rw [hN89]; exact trialForm_eq 1 k89 5 x2Trial_211 (by decide) rfl) chk89

end ThreeCopyQutritWerner.X2.InK1x237
