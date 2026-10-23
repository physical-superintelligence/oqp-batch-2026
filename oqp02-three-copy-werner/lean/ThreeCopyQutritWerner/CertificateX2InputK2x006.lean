module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (0, 0, 6) of sector 2, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK2x006
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k3 : x2Key 2 := ⟨3, by decide⟩
x2_gj_cols gj294 294 2 0 0 6 256
theorem gjc3_0 : (List.range 1).all (fun d => gjCheck 256 2 0 0 6 1 1 11 (x2JCols 294 (0 + d)) (gj294.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok3 : ∀ d < x2KeySize 2 k3, gjCheck 256 2 (x2KeyTypes 2 k3 0) (x2KeyTypes 2 k3 1) (x2KeyTypes 2 k3 2) (x2KeyMult 2 k3 0) (x2KeyMult 2 k3 1) (x2KeyMult 2 k3 2) (x2JCols (x2KeyGlobal 2 k3) d) (gj294.getD d 0) = true := by
  have hr : x2KeySize 2 k3 = 1 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 0 0 6 1 1 11 (x2JCols 294 d) (gj294.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 0 0 6 1 1 11 (x2JCols 294 d) (gj294.getD d 0)) 0 1 gjc3_0 d (Nat.zero_le d) (by omega)
x2_v_cols v294 gj294 294 256 11
theorem vc3_0 : (List.range 1).all (fun c => vCheck 256 11 1 gj294 (x2Trial_294.getD (0 + c) 0) (v294.getD (0 + c) 0)) = true := by decide +kernel
theorem vok3 : ∀ c < 1, vCheck 256 (x2KeyMult 2 k3 0 * x2KeyMult 2 k3 1 * x2KeyMult 2 k3 2) (x2KeySize 2 k3) gj294 (x2Trial_294.getD c 0) (v294.getD c 0) = true := by
  intro c hc
  show vCheck 256 11 1 gj294 (x2Trial_294.getD c 0) (v294.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 11 1 gj294 (x2Trial_294.getD c 0) (v294.getD c 0)) 0 1 vc3_0 c (Nat.zero_le c) (by omega)
theorem small3 : x2KeyDegree 2 k3 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k3 0 ∧ 1 ≤ x2KeyMult 2 k3 1 ∧ 1 ≤ x2KeyMult 2 k3 2 ∧ glRowOK 2 (x2KeyTypes 2 k3 0) (x2KeyMult 2 k3 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k3 1) (x2KeyMult 2 k3 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k3 2) (x2KeyMult 2 k3 2) 512 = true ∧ gj294.length = x2KeySize 2 k3 ∧ x2KeySize 2 k3 ≤ 512 ∧ v294.length = 1 := by decide +kernel
theorem chk3 : trialKeyChk 2 k3 1 gj294 x2Trial_294 v294 :=
  trialKeyChk_intro 2 k3 1 gj294 x2Trial_294 v294 small3 gjok3 vok3

noncomputable def ks : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := [(k3, ibFS [(v294, v294, 94810963968000)])]
theorem hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![0, 0, 6] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 2) (hN3 : N k3 = x2TrialForm 2 k3) :
    ∀ e ∈ ks, keyOK (x2Mult 2 0 * x2Mult 2 0 * x2Mult 2 6) 2 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_singleton] at he
  subst he
  exact keyOK_of_trialChk 2 N k3 1 _ gj294 x2Trial_294 v294 (by decide) (by rw [hN3]; exact trialForm_eq 2 k3 1 x2Trial_294 (by decide) rfl) chk3

end ThreeCopyQutritWerner.X2.InK2x006
