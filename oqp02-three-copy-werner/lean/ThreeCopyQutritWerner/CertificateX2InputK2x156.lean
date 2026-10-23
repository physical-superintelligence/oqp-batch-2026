module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (1, 5, 6) of sector 2, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK2x156
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k57 : x2Key 2 := ⟨57, by decide⟩
x2_gj_cols gj348 348 2 1 5 6 256
theorem gjc57_0 : (List.range 36).all (fun d => gjCheck 256 2 1 5 6 4 10 11 (x2JCols 348 (0 + d)) (gj348.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok57 : ∀ d < x2KeySize 2 k57, gjCheck 256 2 (x2KeyTypes 2 k57 0) (x2KeyTypes 2 k57 1) (x2KeyTypes 2 k57 2) (x2KeyMult 2 k57 0) (x2KeyMult 2 k57 1) (x2KeyMult 2 k57 2) (x2JCols (x2KeyGlobal 2 k57) d) (gj348.getD d 0) = true := by
  have hr : x2KeySize 2 k57 = 36 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 1 5 6 4 10 11 (x2JCols 348 d) (gj348.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 1 5 6 4 10 11 (x2JCols 348 d) (gj348.getD d 0)) 0 36 gjc57_0 d (Nat.zero_le d) (by omega)
x2_v_cols v348 gj348 348 256 440
theorem vc57_0 : (List.range 35).all (fun c => vCheck 256 440 36 gj348 (x2Trial_348.getD (0 + c) 0) (v348.getD (0 + c) 0)) = true := by decide +kernel
theorem vok57 : ∀ c < 35, vCheck 256 (x2KeyMult 2 k57 0 * x2KeyMult 2 k57 1 * x2KeyMult 2 k57 2) (x2KeySize 2 k57) gj348 (x2Trial_348.getD c 0) (v348.getD c 0) = true := by
  intro c hc
  show vCheck 256 440 36 gj348 (x2Trial_348.getD c 0) (v348.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 440 36 gj348 (x2Trial_348.getD c 0) (v348.getD c 0)) 0 35 vc57_0 c (Nat.zero_le c) (by omega)
theorem small57 : x2KeyDegree 2 k57 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k57 0 ∧ 1 ≤ x2KeyMult 2 k57 1 ∧ 1 ≤ x2KeyMult 2 k57 2 ∧ glRowOK 2 (x2KeyTypes 2 k57 0) (x2KeyMult 2 k57 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k57 1) (x2KeyMult 2 k57 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k57 2) (x2KeyMult 2 k57 2) 512 = true ∧ gj348.length = x2KeySize 2 k57 ∧ x2KeySize 2 k57 ≤ 512 ∧ v348.length = 35 := by decide +kernel
theorem chk57 : trialKeyChk 2 k57 35 gj348 x2Trial_348 v348 :=
  trialKeyChk_intro 2 k57 35 gj348 x2Trial_348 v348 small57 gjok57 vok57

noncomputable def ks : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := [(k57, ibFS [(v348, v348, 94810963968000)])]
theorem hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![1, 5, 6] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 2) (hN57 : N k57 = x2TrialForm 2 k57) :
    ∀ e ∈ ks, keyOK (x2Mult 2 1 * x2Mult 2 5 * x2Mult 2 6) 2 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_singleton] at he
  subst he
  exact keyOK_of_trialChk 2 N k57 35 _ gj348 x2Trial_348 v348 (by decide) (by rw [hN57]; exact trialForm_eq 2 k57 35 x2Trial_348 (by decide) rfl) chk57

end ThreeCopyQutritWerner.X2.InK2x156
