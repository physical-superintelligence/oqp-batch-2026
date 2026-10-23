module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (3, 4, 5) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x345
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k117 : x2Key 1 := ⟨117, by decide⟩
x2_gj_cols gj239 239 1 3 4 5 256
theorem gjc117_0 : (List.range 75).all (fun d => gjCheck 256 1 3 4 5 9 7 7 (x2JCols 239 (0 + d)) (gj239.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok117 : ∀ d < x2KeySize 1 k117, gjCheck 256 1 (x2KeyTypes 1 k117 0) (x2KeyTypes 1 k117 1) (x2KeyTypes 1 k117 2) (x2KeyMult 1 k117 0) (x2KeyMult 1 k117 1) (x2KeyMult 1 k117 2) (x2JCols (x2KeyGlobal 1 k117) d) (gj239.getD d 0) = true := by
  have hr : x2KeySize 1 k117 = 75 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 3 4 5 9 7 7 (x2JCols 239 d) (gj239.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 3 4 5 9 7 7 (x2JCols 239 d) (gj239.getD d 0)) 0 75 gjc117_0 d (Nat.zero_le d) (by omega)
x2_v_cols v239 gj239 239 256 441
theorem vc117_0 : (List.range 37).all (fun c => vCheck 256 441 75 gj239 (x2Trial_239.getD (0 + c) 0) (v239.getD (0 + c) 0)) = true := by decide +kernel
theorem vok117 : ∀ c < 37, vCheck 256 (x2KeyMult 1 k117 0 * x2KeyMult 1 k117 1 * x2KeyMult 1 k117 2) (x2KeySize 1 k117) gj239 (x2Trial_239.getD c 0) (v239.getD c 0) = true := by
  intro c hc
  show vCheck 256 441 75 gj239 (x2Trial_239.getD c 0) (v239.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 441 75 gj239 (x2Trial_239.getD c 0) (v239.getD c 0)) 0 37 vc117_0 c (Nat.zero_le c) (by omega)
theorem small117 : x2KeyDegree 1 k117 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k117 0 ∧ 1 ≤ x2KeyMult 1 k117 1 ∧ 1 ≤ x2KeyMult 1 k117 2 ∧ glRowOK 1 (x2KeyTypes 1 k117 0) (x2KeyMult 1 k117 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k117 1) (x2KeyMult 1 k117 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k117 2) (x2KeyMult 1 k117 2) 512 = true ∧ gj239.length = x2KeySize 1 k117 ∧ x2KeySize 1 k117 ≤ 512 ∧ v239.length = 37 := by decide +kernel
theorem chk117 : trialKeyChk 1 k117 37 gj239 x2Trial_239 v239 :=
  trialKeyChk_intro 1 k117 37 gj239 x2Trial_239 v239 small117 gjok117 vok117

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k117, ibFS [(v239, v239, 94810963968000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![3, 4, 5] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN117 : N k117 = x2TrialForm 1 k117) :
    ∀ e ∈ ks, keyOK (x2Mult 1 3 * x2Mult 1 4 * x2Mult 1 5) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_singleton] at he
  subst he
  exact keyOK_of_trialChk 1 N k117 37 _ gj239 x2Trial_239 v239 (by decide) (by rw [hN117]; exact trialForm_eq 1 k117 37 x2Trial_239 (by decide) rfl) chk117

end ThreeCopyQutritWerner.X2.InK1x345
