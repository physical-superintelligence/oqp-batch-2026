module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (0, 6, 7) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x067
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k33 : x2Key 1 := ⟨33, by decide⟩
x2_gj_cols gj155 155 1 0 6 7 256
theorem gjc33_0 : (List.range 17).all (fun d => gjCheck 256 1 0 6 7 1 17 6 (x2JCols 155 (0 + d)) (gj155.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok33 : ∀ d < x2KeySize 1 k33, gjCheck 256 1 (x2KeyTypes 1 k33 0) (x2KeyTypes 1 k33 1) (x2KeyTypes 1 k33 2) (x2KeyMult 1 k33 0) (x2KeyMult 1 k33 1) (x2KeyMult 1 k33 2) (x2JCols (x2KeyGlobal 1 k33) d) (gj155.getD d 0) = true := by
  have hr : x2KeySize 1 k33 = 17 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 0 6 7 1 17 6 (x2JCols 155 d) (gj155.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 0 6 7 1 17 6 (x2JCols 155 d) (gj155.getD d 0)) 0 17 gjc33_0 d (Nat.zero_le d) (by omega)
x2_v_cols v155 gj155 155 256 102
theorem vc33_0 : (List.range 7).all (fun c => vCheck 256 102 17 gj155 (x2Trial_155.getD (0 + c) 0) (v155.getD (0 + c) 0)) = true := by decide +kernel
theorem vok33 : ∀ c < 7, vCheck 256 (x2KeyMult 1 k33 0 * x2KeyMult 1 k33 1 * x2KeyMult 1 k33 2) (x2KeySize 1 k33) gj155 (x2Trial_155.getD c 0) (v155.getD c 0) = true := by
  intro c hc
  show vCheck 256 102 17 gj155 (x2Trial_155.getD c 0) (v155.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 102 17 gj155 (x2Trial_155.getD c 0) (v155.getD c 0)) 0 7 vc33_0 c (Nat.zero_le c) (by omega)
theorem small33 : x2KeyDegree 1 k33 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k33 0 ∧ 1 ≤ x2KeyMult 1 k33 1 ∧ 1 ≤ x2KeyMult 1 k33 2 ∧ glRowOK 1 (x2KeyTypes 1 k33 0) (x2KeyMult 1 k33 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k33 1) (x2KeyMult 1 k33 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k33 2) (x2KeyMult 1 k33 2) 512 = true ∧ gj155.length = x2KeySize 1 k33 ∧ x2KeySize 1 k33 ≤ 512 ∧ v155.length = 7 := by decide +kernel
theorem chk33 : trialKeyChk 1 k33 7 gj155 x2Trial_155 v155 :=
  trialKeyChk_intro 1 k33 7 gj155 x2Trial_155 v155 small33 gjok33 vok33

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k33, ibFS [(v155, v155, 94810963968000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![0, 6, 7] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN33 : N k33 = x2TrialForm 1 k33) :
    ∀ e ∈ ks, keyOK (x2Mult 1 0 * x2Mult 1 6 * x2Mult 1 7) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_singleton] at he
  subst he
  exact keyOK_of_trialChk 1 N k33 7 _ gj155 x2Trial_155 v155 (by decide) (by rw [hN33]; exact trialForm_eq 1 k33 7 x2Trial_155 (by decide) rfl) chk33

end ThreeCopyQutritWerner.X2.InK1x067
