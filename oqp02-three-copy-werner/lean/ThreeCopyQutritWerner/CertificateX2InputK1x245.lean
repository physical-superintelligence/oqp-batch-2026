module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (2, 4, 5) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x245
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k92 : x2Key 1 := ⟨92, by decide⟩
x2_gj_cols gj214 214 1 2 4 5 256
theorem gjc92_0 : (List.range 17).all (fun d => gjCheck 256 1 2 4 5 2 7 7 (x2JCols 214 (0 + d)) (gj214.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok92 : ∀ d < x2KeySize 1 k92, gjCheck 256 1 (x2KeyTypes 1 k92 0) (x2KeyTypes 1 k92 1) (x2KeyTypes 1 k92 2) (x2KeyMult 1 k92 0) (x2KeyMult 1 k92 1) (x2KeyMult 1 k92 2) (x2JCols (x2KeyGlobal 1 k92) d) (gj214.getD d 0) = true := by
  have hr : x2KeySize 1 k92 = 17 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 2 4 5 2 7 7 (x2JCols 214 d) (gj214.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 2 4 5 2 7 7 (x2JCols 214 d) (gj214.getD d 0)) 0 17 gjc92_0 d (Nat.zero_le d) (by omega)
x2_v_cols v214 gj214 214 256 98
theorem vc92_0 : (List.range 7).all (fun c => vCheck 256 98 17 gj214 (x2Trial_214.getD (0 + c) 0) (v214.getD (0 + c) 0)) = true := by decide +kernel
theorem vok92 : ∀ c < 7, vCheck 256 (x2KeyMult 1 k92 0 * x2KeyMult 1 k92 1 * x2KeyMult 1 k92 2) (x2KeySize 1 k92) gj214 (x2Trial_214.getD c 0) (v214.getD c 0) = true := by
  intro c hc
  show vCheck 256 98 17 gj214 (x2Trial_214.getD c 0) (v214.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 98 17 gj214 (x2Trial_214.getD c 0) (v214.getD c 0)) 0 7 vc92_0 c (Nat.zero_le c) (by omega)
theorem small92 : x2KeyDegree 1 k92 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k92 0 ∧ 1 ≤ x2KeyMult 1 k92 1 ∧ 1 ≤ x2KeyMult 1 k92 2 ∧ glRowOK 1 (x2KeyTypes 1 k92 0) (x2KeyMult 1 k92 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k92 1) (x2KeyMult 1 k92 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k92 2) (x2KeyMult 1 k92 2) 512 = true ∧ gj214.length = x2KeySize 1 k92 ∧ x2KeySize 1 k92 ≤ 512 ∧ v214.length = 7 := by decide +kernel
theorem chk92 : trialKeyChk 1 k92 7 gj214 x2Trial_214 v214 :=
  trialKeyChk_intro 1 k92 7 gj214 x2Trial_214 v214 small92 gjok92 vok92

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k92, ibFS [(v214, v214, 94810963968000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![2, 4, 5] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN92 : N k92 = x2TrialForm 1 k92) :
    ∀ e ∈ ks, keyOK (x2Mult 1 2 * x2Mult 1 4 * x2Mult 1 5) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_singleton] at he
  subst he
  exact keyOK_of_trialChk 1 N k92 7 _ gj214 x2Trial_214 v214 (by decide) (by rw [hN92]; exact trialForm_eq 1 k92 7 x2Trial_214 (by decide) rfl) chk92

end ThreeCopyQutritWerner.X2.InK1x245
