module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (2, 3, 4) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x234
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k86 : x2Key 1 := ⟨86, by decide⟩
x2_gj_cols gj208 208 1 2 3 4 256
theorem gjc86_0 : (List.range 22).all (fun d => gjCheck 256 1 2 3 4 2 9 7 (x2JCols 208 (0 + d)) (gj208.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok86 : ∀ d < x2KeySize 1 k86, gjCheck 256 1 (x2KeyTypes 1 k86 0) (x2KeyTypes 1 k86 1) (x2KeyTypes 1 k86 2) (x2KeyMult 1 k86 0) (x2KeyMult 1 k86 1) (x2KeyMult 1 k86 2) (x2JCols (x2KeyGlobal 1 k86) d) (gj208.getD d 0) = true := by
  have hr : x2KeySize 1 k86 = 22 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 2 3 4 2 9 7 (x2JCols 208 d) (gj208.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 2 3 4 2 9 7 (x2JCols 208 d) (gj208.getD d 0)) 0 22 gjc86_0 d (Nat.zero_le d) (by omega)
x2_v_cols v208 gj208 208 256 126
theorem vc86_0 : (List.range 5).all (fun c => vCheck 256 126 22 gj208 (x2Trial_208.getD (0 + c) 0) (v208.getD (0 + c) 0)) = true := by decide +kernel
theorem vok86 : ∀ c < 5, vCheck 256 (x2KeyMult 1 k86 0 * x2KeyMult 1 k86 1 * x2KeyMult 1 k86 2) (x2KeySize 1 k86) gj208 (x2Trial_208.getD c 0) (v208.getD c 0) = true := by
  intro c hc
  show vCheck 256 126 22 gj208 (x2Trial_208.getD c 0) (v208.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 126 22 gj208 (x2Trial_208.getD c 0) (v208.getD c 0)) 0 5 vc86_0 c (Nat.zero_le c) (by omega)
theorem small86 : x2KeyDegree 1 k86 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k86 0 ∧ 1 ≤ x2KeyMult 1 k86 1 ∧ 1 ≤ x2KeyMult 1 k86 2 ∧ glRowOK 1 (x2KeyTypes 1 k86 0) (x2KeyMult 1 k86 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k86 1) (x2KeyMult 1 k86 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k86 2) (x2KeyMult 1 k86 2) 512 = true ∧ gj208.length = x2KeySize 1 k86 ∧ x2KeySize 1 k86 ≤ 512 ∧ v208.length = 5 := by decide +kernel
theorem chk86 : trialKeyChk 1 k86 5 gj208 x2Trial_208 v208 :=
  trialKeyChk_intro 1 k86 5 gj208 x2Trial_208 v208 small86 gjok86 vok86

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k86, ibFS [(v208, v208, 94810963968000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![2, 3, 4] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN86 : N k86 = x2TrialForm 1 k86) :
    ∀ e ∈ ks, keyOK (x2Mult 1 2 * x2Mult 1 3 * x2Mult 1 4) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_singleton] at he
  subst he
  exact keyOK_of_trialChk 1 N k86 5 _ gj208 x2Trial_208 v208 (by decide) (by rw [hN86]; exact trialForm_eq 1 k86 5 x2Trial_208 (by decide) rfl) chk86

end ThreeCopyQutritWerner.X2.InK1x234
