module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (2, 3, 6) of sector 2, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK2x236
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k74 : x2Key 2 := ⟨74, by decide⟩
x2_gj_cols gj365 365 2 2 3 6 256
theorem gjc74_0 : (List.range 22).all (fun d => gjCheck 256 2 2 3 6 5 5 11 (x2JCols 365 (0 + d)) (gj365.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok74 : ∀ d < x2KeySize 2 k74, gjCheck 256 2 (x2KeyTypes 2 k74 0) (x2KeyTypes 2 k74 1) (x2KeyTypes 2 k74 2) (x2KeyMult 2 k74 0) (x2KeyMult 2 k74 1) (x2KeyMult 2 k74 2) (x2JCols (x2KeyGlobal 2 k74) d) (gj365.getD d 0) = true := by
  have hr : x2KeySize 2 k74 = 22 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 2 3 6 5 5 11 (x2JCols 365 d) (gj365.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 2 3 6 5 5 11 (x2JCols 365 d) (gj365.getD d 0)) 0 22 gjc74_0 d (Nat.zero_le d) (by omega)
x2_v_cols v365 gj365 365 256 275
theorem vc74_0 : (List.range 21).all (fun c => vCheck 256 275 22 gj365 (x2Trial_365.getD (0 + c) 0) (v365.getD (0 + c) 0)) = true := by decide +kernel
theorem vok74 : ∀ c < 21, vCheck 256 (x2KeyMult 2 k74 0 * x2KeyMult 2 k74 1 * x2KeyMult 2 k74 2) (x2KeySize 2 k74) gj365 (x2Trial_365.getD c 0) (v365.getD c 0) = true := by
  intro c hc
  show vCheck 256 275 22 gj365 (x2Trial_365.getD c 0) (v365.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 275 22 gj365 (x2Trial_365.getD c 0) (v365.getD c 0)) 0 21 vc74_0 c (Nat.zero_le c) (by omega)
theorem small74 : x2KeyDegree 2 k74 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k74 0 ∧ 1 ≤ x2KeyMult 2 k74 1 ∧ 1 ≤ x2KeyMult 2 k74 2 ∧ glRowOK 2 (x2KeyTypes 2 k74 0) (x2KeyMult 2 k74 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k74 1) (x2KeyMult 2 k74 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k74 2) (x2KeyMult 2 k74 2) 512 = true ∧ gj365.length = x2KeySize 2 k74 ∧ x2KeySize 2 k74 ≤ 512 ∧ v365.length = 21 := by decide +kernel
theorem chk74 : trialKeyChk 2 k74 21 gj365 x2Trial_365 v365 :=
  trialKeyChk_intro 2 k74 21 gj365 x2Trial_365 v365 small74 gjok74 vok74

noncomputable def ks : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := [(k74, ibFS [(v365, v365, 94810963968000)])]
theorem hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![2, 3, 6] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 2) (hN74 : N k74 = x2TrialForm 2 k74) :
    ∀ e ∈ ks, keyOK (x2Mult 2 2 * x2Mult 2 3 * x2Mult 2 6) 2 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_singleton] at he
  subst he
  exact keyOK_of_trialChk 2 N k74 21 _ gj365 x2Trial_365 v365 (by decide) (by rw [hN74]; exact trialForm_eq 2 k74 21 x2Trial_365 (by decide) rfl) chk74

end ThreeCopyQutritWerner.X2.InK2x236
