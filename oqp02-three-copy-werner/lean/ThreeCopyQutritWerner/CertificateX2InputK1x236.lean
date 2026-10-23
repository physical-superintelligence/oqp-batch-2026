module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (2, 3, 6) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x236
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k88 : x2Key 1 := ⟨88, by decide⟩
x2_gj_cols gj210 210 1 2 3 6 256
theorem gjc88_0 : (List.range 50).all (fun d => gjCheck 256 1 2 3 6 2 9 17 (x2JCols 210 (0 + d)) (gj210.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok88 : ∀ d < x2KeySize 1 k88, gjCheck 256 1 (x2KeyTypes 1 k88 0) (x2KeyTypes 1 k88 1) (x2KeyTypes 1 k88 2) (x2KeyMult 1 k88 0) (x2KeyMult 1 k88 1) (x2KeyMult 1 k88 2) (x2JCols (x2KeyGlobal 1 k88) d) (gj210.getD d 0) = true := by
  have hr : x2KeySize 1 k88 = 50 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 2 3 6 2 9 17 (x2JCols 210 d) (gj210.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 2 3 6 2 9 17 (x2JCols 210 d) (gj210.getD d 0)) 0 50 gjc88_0 d (Nat.zero_le d) (by omega)
x2_v_cols v210 gj210 210 256 306
theorem vc88_0 : (List.range 16).all (fun c => vCheck 256 306 50 gj210 (x2Trial_210.getD (0 + c) 0) (v210.getD (0 + c) 0)) = true := by decide +kernel
theorem vok88 : ∀ c < 16, vCheck 256 (x2KeyMult 1 k88 0 * x2KeyMult 1 k88 1 * x2KeyMult 1 k88 2) (x2KeySize 1 k88) gj210 (x2Trial_210.getD c 0) (v210.getD c 0) = true := by
  intro c hc
  show vCheck 256 306 50 gj210 (x2Trial_210.getD c 0) (v210.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 306 50 gj210 (x2Trial_210.getD c 0) (v210.getD c 0)) 0 16 vc88_0 c (Nat.zero_le c) (by omega)
theorem small88 : x2KeyDegree 1 k88 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k88 0 ∧ 1 ≤ x2KeyMult 1 k88 1 ∧ 1 ≤ x2KeyMult 1 k88 2 ∧ glRowOK 1 (x2KeyTypes 1 k88 0) (x2KeyMult 1 k88 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k88 1) (x2KeyMult 1 k88 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k88 2) (x2KeyMult 1 k88 2) 512 = true ∧ gj210.length = x2KeySize 1 k88 ∧ x2KeySize 1 k88 ≤ 512 ∧ v210.length = 16 := by decide +kernel
theorem chk88 : trialKeyChk 1 k88 16 gj210 x2Trial_210 v210 :=
  trialKeyChk_intro 1 k88 16 gj210 x2Trial_210 v210 small88 gjok88 vok88

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k88, ibFS [(v210, v210, 94810963968000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![2, 3, 6] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN88 : N k88 = x2TrialForm 1 k88) :
    ∀ e ∈ ks, keyOK (x2Mult 1 2 * x2Mult 1 3 * x2Mult 1 6) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_singleton] at he
  subst he
  exact keyOK_of_trialChk 1 N k88 16 _ gj210 x2Trial_210 v210 (by decide) (by rw [hN88]; exact trialForm_eq 1 k88 16 x2Trial_210 (by decide) rfl) chk88

end ThreeCopyQutritWerner.X2.InK1x236
