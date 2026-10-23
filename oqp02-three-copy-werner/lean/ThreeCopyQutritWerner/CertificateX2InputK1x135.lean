module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (1, 3, 5) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x135
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k57 : x2Key 1 := ⟨57, by decide⟩
x2_gj_cols gj179 179 1 1 3 5 256
theorem gjc57_0 : (List.range 21).all (fun d => gjCheck 256 1 1 3 5 2 9 7 (x2JCols 179 (0 + d)) (gj179.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok57 : ∀ d < x2KeySize 1 k57, gjCheck 256 1 (x2KeyTypes 1 k57 0) (x2KeyTypes 1 k57 1) (x2KeyTypes 1 k57 2) (x2KeyMult 1 k57 0) (x2KeyMult 1 k57 1) (x2KeyMult 1 k57 2) (x2JCols (x2KeyGlobal 1 k57) d) (gj179.getD d 0) = true := by
  have hr : x2KeySize 1 k57 = 21 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 1 3 5 2 9 7 (x2JCols 179 d) (gj179.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 1 3 5 2 9 7 (x2JCols 179 d) (gj179.getD d 0)) 0 21 gjc57_0 d (Nat.zero_le d) (by omega)
x2_v_cols v179 gj179 179 256 126
theorem vc57_0 : (List.range 3).all (fun c => vCheck 256 126 21 gj179 (x2Trial_179.getD (0 + c) 0) (v179.getD (0 + c) 0)) = true := by decide +kernel
theorem vok57 : ∀ c < 3, vCheck 256 (x2KeyMult 1 k57 0 * x2KeyMult 1 k57 1 * x2KeyMult 1 k57 2) (x2KeySize 1 k57) gj179 (x2Trial_179.getD c 0) (v179.getD c 0) = true := by
  intro c hc
  show vCheck 256 126 21 gj179 (x2Trial_179.getD c 0) (v179.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 126 21 gj179 (x2Trial_179.getD c 0) (v179.getD c 0)) 0 3 vc57_0 c (Nat.zero_le c) (by omega)
theorem small57 : x2KeyDegree 1 k57 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k57 0 ∧ 1 ≤ x2KeyMult 1 k57 1 ∧ 1 ≤ x2KeyMult 1 k57 2 ∧ glRowOK 1 (x2KeyTypes 1 k57 0) (x2KeyMult 1 k57 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k57 1) (x2KeyMult 1 k57 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k57 2) (x2KeyMult 1 k57 2) 512 = true ∧ gj179.length = x2KeySize 1 k57 ∧ x2KeySize 1 k57 ≤ 512 ∧ v179.length = 3 := by decide +kernel
theorem chk57 : trialKeyChk 1 k57 3 gj179 x2Trial_179 v179 :=
  trialKeyChk_intro 1 k57 3 gj179 x2Trial_179 v179 small57 gjok57 vok57

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k57, ibFS [(v179, v179, 94810963968000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![1, 3, 5] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN57 : N k57 = x2TrialForm 1 k57) :
    ∀ e ∈ ks, keyOK (x2Mult 1 1 * x2Mult 1 3 * x2Mult 1 5) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_singleton] at he
  subst he
  exact keyOK_of_trialChk 1 N k57 3 _ gj179 x2Trial_179 v179 (by decide) (by rw [hN57]; exact trialForm_eq 1 k57 3 x2Trial_179 (by decide) rfl) chk57

end ThreeCopyQutritWerner.X2.InK1x135
