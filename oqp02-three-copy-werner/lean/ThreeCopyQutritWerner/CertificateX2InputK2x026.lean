module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (0, 2, 6) of sector 2, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK2x026
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k14 : x2Key 2 := ⟨14, by decide⟩
x2_gj_cols gj305 305 2 0 2 6 256
theorem gjc14_0 : (List.range 5).all (fun d => gjCheck 256 2 0 2 6 1 5 11 (x2JCols 305 (0 + d)) (gj305.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok14 : ∀ d < x2KeySize 2 k14, gjCheck 256 2 (x2KeyTypes 2 k14 0) (x2KeyTypes 2 k14 1) (x2KeyTypes 2 k14 2) (x2KeyMult 2 k14 0) (x2KeyMult 2 k14 1) (x2KeyMult 2 k14 2) (x2JCols (x2KeyGlobal 2 k14) d) (gj305.getD d 0) = true := by
  have hr : x2KeySize 2 k14 = 5 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 0 2 6 1 5 11 (x2JCols 305 d) (gj305.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 0 2 6 1 5 11 (x2JCols 305 d) (gj305.getD d 0)) 0 5 gjc14_0 d (Nat.zero_le d) (by omega)
x2_v_cols v305 gj305 305 256 55
theorem vc14_0 : (List.range 5).all (fun c => vCheck 256 55 5 gj305 (x2Trial_305.getD (0 + c) 0) (v305.getD (0 + c) 0)) = true := by decide +kernel
theorem vok14 : ∀ c < 5, vCheck 256 (x2KeyMult 2 k14 0 * x2KeyMult 2 k14 1 * x2KeyMult 2 k14 2) (x2KeySize 2 k14) gj305 (x2Trial_305.getD c 0) (v305.getD c 0) = true := by
  intro c hc
  show vCheck 256 55 5 gj305 (x2Trial_305.getD c 0) (v305.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 55 5 gj305 (x2Trial_305.getD c 0) (v305.getD c 0)) 0 5 vc14_0 c (Nat.zero_le c) (by omega)
theorem small14 : x2KeyDegree 2 k14 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k14 0 ∧ 1 ≤ x2KeyMult 2 k14 1 ∧ 1 ≤ x2KeyMult 2 k14 2 ∧ glRowOK 2 (x2KeyTypes 2 k14 0) (x2KeyMult 2 k14 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k14 1) (x2KeyMult 2 k14 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k14 2) (x2KeyMult 2 k14 2) 512 = true ∧ gj305.length = x2KeySize 2 k14 ∧ x2KeySize 2 k14 ≤ 512 ∧ v305.length = 5 := by decide +kernel
theorem chk14 : trialKeyChk 2 k14 5 gj305 x2Trial_305 v305 :=
  trialKeyChk_intro 2 k14 5 gj305 x2Trial_305 v305 small14 gjok14 vok14

noncomputable def ks : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := [(k14, ibFS [(v305, v305, 94810963968000)])]
theorem hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![0, 2, 6] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 2) (hN14 : N k14 = x2TrialForm 2 k14) :
    ∀ e ∈ ks, keyOK (x2Mult 2 0 * x2Mult 2 2 * x2Mult 2 6) 2 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_singleton] at he
  subst he
  exact keyOK_of_trialChk 2 N k14 5 _ gj305 x2Trial_305 v305 (by decide) (by rw [hN14]; exact trialForm_eq 2 k14 5 x2Trial_305 (by decide) rfl) chk14

end ThreeCopyQutritWerner.X2.InK2x026
