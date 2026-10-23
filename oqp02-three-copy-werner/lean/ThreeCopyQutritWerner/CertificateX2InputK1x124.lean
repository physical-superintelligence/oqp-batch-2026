module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (1, 2, 4) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x124
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k50 : x2Key 1 := ⟨50, by decide⟩
x2_gj_cols gj172 172 1 1 2 4 256
theorem gjc50_0 : (List.range 5).all (fun d => gjCheck 256 1 1 2 4 2 2 7 (x2JCols 172 (0 + d)) (gj172.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok50 : ∀ d < x2KeySize 1 k50, gjCheck 256 1 (x2KeyTypes 1 k50 0) (x2KeyTypes 1 k50 1) (x2KeyTypes 1 k50 2) (x2KeyMult 1 k50 0) (x2KeyMult 1 k50 1) (x2KeyMult 1 k50 2) (x2JCols (x2KeyGlobal 1 k50) d) (gj172.getD d 0) = true := by
  have hr : x2KeySize 1 k50 = 5 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 1 2 4 2 2 7 (x2JCols 172 d) (gj172.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 1 2 4 2 2 7 (x2JCols 172 d) (gj172.getD d 0)) 0 5 gjc50_0 d (Nat.zero_le d) (by omega)
x2_v_cols v172 gj172 172 256 28
theorem vc50_0 : (List.range 1).all (fun c => vCheck 256 28 5 gj172 (x2Trial_172.getD (0 + c) 0) (v172.getD (0 + c) 0)) = true := by decide +kernel
theorem vok50 : ∀ c < 1, vCheck 256 (x2KeyMult 1 k50 0 * x2KeyMult 1 k50 1 * x2KeyMult 1 k50 2) (x2KeySize 1 k50) gj172 (x2Trial_172.getD c 0) (v172.getD c 0) = true := by
  intro c hc
  show vCheck 256 28 5 gj172 (x2Trial_172.getD c 0) (v172.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 28 5 gj172 (x2Trial_172.getD c 0) (v172.getD c 0)) 0 1 vc50_0 c (Nat.zero_le c) (by omega)
theorem small50 : x2KeyDegree 1 k50 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k50 0 ∧ 1 ≤ x2KeyMult 1 k50 1 ∧ 1 ≤ x2KeyMult 1 k50 2 ∧ glRowOK 1 (x2KeyTypes 1 k50 0) (x2KeyMult 1 k50 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k50 1) (x2KeyMult 1 k50 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k50 2) (x2KeyMult 1 k50 2) 512 = true ∧ gj172.length = x2KeySize 1 k50 ∧ x2KeySize 1 k50 ≤ 512 ∧ v172.length = 1 := by decide +kernel
theorem chk50 : trialKeyChk 1 k50 1 gj172 x2Trial_172 v172 :=
  trialKeyChk_intro 1 k50 1 gj172 x2Trial_172 v172 small50 gjok50 vok50

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k50, ibFS [(v172, v172, 94810963968000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![1, 2, 4] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN50 : N k50 = x2TrialForm 1 k50) :
    ∀ e ∈ ks, keyOK (x2Mult 1 1 * x2Mult 1 2 * x2Mult 1 4) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_singleton] at he
  subst he
  exact keyOK_of_trialChk 1 N k50 1 _ gj172 x2Trial_172 v172 (by decide) (by rw [hN50]; exact trialForm_eq 1 k50 1 x2Trial_172 (by decide) rfl) chk50

end ThreeCopyQutritWerner.X2.InK1x124
