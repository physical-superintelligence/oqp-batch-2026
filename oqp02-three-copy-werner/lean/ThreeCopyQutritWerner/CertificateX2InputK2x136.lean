module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (1, 3, 6) of sector 2, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK2x136
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k50 : x2Key 2 := ⟨50, by decide⟩
x2_gj_cols gj341 341 2 1 3 6 256
theorem gjc50_0 : (List.range 18).all (fun d => gjCheck 256 2 1 3 6 4 5 11 (x2JCols 341 (0 + d)) (gj341.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok50 : ∀ d < x2KeySize 2 k50, gjCheck 256 2 (x2KeyTypes 2 k50 0) (x2KeyTypes 2 k50 1) (x2KeyTypes 2 k50 2) (x2KeyMult 2 k50 0) (x2KeyMult 2 k50 1) (x2KeyMult 2 k50 2) (x2JCols (x2KeyGlobal 2 k50) d) (gj341.getD d 0) = true := by
  have hr : x2KeySize 2 k50 = 18 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 1 3 6 4 5 11 (x2JCols 341 d) (gj341.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 1 3 6 4 5 11 (x2JCols 341 d) (gj341.getD d 0)) 0 18 gjc50_0 d (Nat.zero_le d) (by omega)
x2_v_cols v341 gj341 341 256 220
theorem vc50_0 : (List.range 17).all (fun c => vCheck 256 220 18 gj341 (x2Trial_341.getD (0 + c) 0) (v341.getD (0 + c) 0)) = true := by decide +kernel
theorem vok50 : ∀ c < 17, vCheck 256 (x2KeyMult 2 k50 0 * x2KeyMult 2 k50 1 * x2KeyMult 2 k50 2) (x2KeySize 2 k50) gj341 (x2Trial_341.getD c 0) (v341.getD c 0) = true := by
  intro c hc
  show vCheck 256 220 18 gj341 (x2Trial_341.getD c 0) (v341.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 220 18 gj341 (x2Trial_341.getD c 0) (v341.getD c 0)) 0 17 vc50_0 c (Nat.zero_le c) (by omega)
theorem small50 : x2KeyDegree 2 k50 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k50 0 ∧ 1 ≤ x2KeyMult 2 k50 1 ∧ 1 ≤ x2KeyMult 2 k50 2 ∧ glRowOK 2 (x2KeyTypes 2 k50 0) (x2KeyMult 2 k50 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k50 1) (x2KeyMult 2 k50 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k50 2) (x2KeyMult 2 k50 2) 512 = true ∧ gj341.length = x2KeySize 2 k50 ∧ x2KeySize 2 k50 ≤ 512 ∧ v341.length = 17 := by decide +kernel
theorem chk50 : trialKeyChk 2 k50 17 gj341 x2Trial_341 v341 :=
  trialKeyChk_intro 2 k50 17 gj341 x2Trial_341 v341 small50 gjok50 vok50

noncomputable def ks : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := [(k50, ibFS [(v341, v341, 94810963968000)])]
theorem hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![1, 3, 6] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 2) (hN50 : N k50 = x2TrialForm 2 k50) :
    ∀ e ∈ ks, keyOK (x2Mult 2 1 * x2Mult 2 3 * x2Mult 2 6) 2 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_singleton] at he
  subst he
  exact keyOK_of_trialChk 2 N k50 17 _ gj341 x2Trial_341 v341 (by decide) (by rw [hN50]; exact trialForm_eq 2 k50 17 x2Trial_341 (by decide) rfl) chk50

end ThreeCopyQutritWerner.X2.InK2x136
