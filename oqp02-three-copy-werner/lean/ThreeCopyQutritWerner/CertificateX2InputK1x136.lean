module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (1, 3, 6) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x136
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k58 : x2Key 1 := ⟨58, by decide⟩
x2_gj_cols gj180 180 1 1 3 6 256
theorem gjc58_0 : (List.range 51).all (fun d => gjCheck 256 1 1 3 6 2 9 17 (x2JCols 180 (0 + d)) (gj180.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok58 : ∀ d < x2KeySize 1 k58, gjCheck 256 1 (x2KeyTypes 1 k58 0) (x2KeyTypes 1 k58 1) (x2KeyTypes 1 k58 2) (x2KeyMult 1 k58 0) (x2KeyMult 1 k58 1) (x2KeyMult 1 k58 2) (x2JCols (x2KeyGlobal 1 k58) d) (gj180.getD d 0) = true := by
  have hr : x2KeySize 1 k58 = 51 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 1 3 6 2 9 17 (x2JCols 180 d) (gj180.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 1 3 6 2 9 17 (x2JCols 180 d) (gj180.getD d 0)) 0 51 gjc58_0 d (Nat.zero_le d) (by omega)
x2_v_cols v180 gj180 180 256 306
theorem vc58_0 : (List.range 12).all (fun c => vCheck 256 306 51 gj180 (x2Trial_180.getD (0 + c) 0) (v180.getD (0 + c) 0)) = true := by decide +kernel
theorem vok58 : ∀ c < 12, vCheck 256 (x2KeyMult 1 k58 0 * x2KeyMult 1 k58 1 * x2KeyMult 1 k58 2) (x2KeySize 1 k58) gj180 (x2Trial_180.getD c 0) (v180.getD c 0) = true := by
  intro c hc
  show vCheck 256 306 51 gj180 (x2Trial_180.getD c 0) (v180.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 306 51 gj180 (x2Trial_180.getD c 0) (v180.getD c 0)) 0 12 vc58_0 c (Nat.zero_le c) (by omega)
theorem small58 : x2KeyDegree 1 k58 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k58 0 ∧ 1 ≤ x2KeyMult 1 k58 1 ∧ 1 ≤ x2KeyMult 1 k58 2 ∧ glRowOK 1 (x2KeyTypes 1 k58 0) (x2KeyMult 1 k58 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k58 1) (x2KeyMult 1 k58 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k58 2) (x2KeyMult 1 k58 2) 512 = true ∧ gj180.length = x2KeySize 1 k58 ∧ x2KeySize 1 k58 ≤ 512 ∧ v180.length = 12 := by decide +kernel
theorem chk58 : trialKeyChk 1 k58 12 gj180 x2Trial_180 v180 :=
  trialKeyChk_intro 1 k58 12 gj180 x2Trial_180 v180 small58 gjok58 vok58

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k58, ibFS [(v180, v180, 94810963968000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![1, 3, 6] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN58 : N k58 = x2TrialForm 1 k58) :
    ∀ e ∈ ks, keyOK (x2Mult 1 1 * x2Mult 1 3 * x2Mult 1 6) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_singleton] at he
  subst he
  exact keyOK_of_trialChk 1 N k58 12 _ gj180 x2Trial_180 v180 (by decide) (by rw [hN58]; exact trialForm_eq 1 k58 12 x2Trial_180 (by decide) rfl) chk58

end ThreeCopyQutritWerner.X2.InK1x136
