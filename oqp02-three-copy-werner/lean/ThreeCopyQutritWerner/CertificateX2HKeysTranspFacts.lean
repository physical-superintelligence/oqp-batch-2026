module

public import ThreeCopyQutritWerner.CertificateX2HKeysTransp

@[expose] public section


/-!
# From the packed column checks to the transposition identities of an h image

`rhoG_mul_apply`: an entry of `ρ(p) J` as the triple sum of `colCheck_sound`. `x2hTransp_ids_of_check`:
a passing `keyCheck b` gives the three matrix identities that `x2hCarrierFix` consumes.
-/

set_option maxRecDepth 100000

noncomputable section

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner.X2Sites

open X2

theorem x2hE_symm_val (τ : Fin 7 × Fin 7 × Fin 7) (x : Fin (hsz τ.1) × (Fin (hsz τ.2.1) × Fin (hsz τ.2.2))) :
    (((x2hE τ).symm x : HIdx τ) : ℕ) = ((x.1 : ℕ) * hsz τ.2.1 + x.2.1) * hsz τ.2.2 + x.2.2 := by
  have h := x2hCoords_symm τ x
  rw [x2hCoords_apply] at h
  have e0 := congrFun h 0
  have e1 := congrFun h 1
  have e2 := congrFun h 2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons] at e0 e1 e2
  have hd1 := Nat.div_add_mod (((x2hE τ).symm x : HIdx τ) : ℕ) (hsz τ.2.1 * hsz τ.2.2)
  have hd2 := Nat.div_add_mod ((((x2hE τ).symm x : HIdx τ) : ℕ) % (hsz τ.2.1 * hsz τ.2.2)) (hsz τ.2.2)
  rw [e0] at hd1
  rw [e1, e2] at hd2
  rw [← hd2] at hd1
  rw [← hd1]
  ring

theorem x2hE_val (τ : Fin 7 × Fin 7 × Fin 7) (i : HIdx τ) :
    (((x2hE τ i).1 : ℕ) * hsz τ.2.1 + (x2hE τ i).2.1) * hsz τ.2.2 + (x2hE τ i).2.2 = (i : ℕ) := by
  rw [← x2hE_symm_val τ (x2hE τ i), Equiv.symm_apply_apply]

theorem x2hAct_ent (p : Fin 120) (t : Fin 7) (y z : Fin (hsz t)) :
    x2hAct p t y z = ((aEnt t p y z : ℤ) : ℂ) := by
  have hy := y.isLt
  have hz := z.isLt
  fin_cases t
  · have hy' : (y : ℕ) < 1 := hy
    have hz' : (z : ℕ) < 1 := hz
    show ((x2hA0 p).map (Int.cast : ℤ → ℂ)) y z = ((aEntT (x2hA0 p) y z : ℤ) : ℂ)
    simp only [aEntT, dif_pos hy', dif_pos hz']
    rfl
  · have hy' : (y : ℕ) < 4 := hy
    have hz' : (z : ℕ) < 4 := hz
    show ((x2hA1 p).map (Int.cast : ℤ → ℂ)) y z = ((aEntT (x2hA1 p) y z : ℤ) : ℂ)
    simp only [aEntT, dif_pos hy', dif_pos hz']
    rfl
  · have hy' : (y : ℕ) < 5 := hy
    have hz' : (z : ℕ) < 5 := hz
    show ((x2hA2 p).map (Int.cast : ℤ → ℂ)) y z = ((aEntT (x2hA2 p) y z : ℤ) : ℂ)
    simp only [aEntT, dif_pos hy', dif_pos hz']
    rfl
  · have hy' : (y : ℕ) < 5 := hy
    have hz' : (z : ℕ) < 5 := hz
    show ((x2hA3 p).map (Int.cast : ℤ → ℂ)) y z = ((aEntT (x2hA3 p) y z : ℤ) : ℂ)
    simp only [aEntT, dif_pos hy', dif_pos hz']
    rfl
  · have hy' : (y : ℕ) < 15 := hy
    have hz' : (z : ℕ) < 15 := hz
    show ((x2hA4 p).map (Int.cast : ℤ → ℂ)) y z = ((aEntT (x2hA4 p) y z : ℤ) : ℂ)
    simp only [aEntT, dif_pos hy', dif_pos hz']
    rfl
  · have hy' : (y : ℕ) < 10 := hy
    have hz' : (z : ℕ) < 10 := hz
    show ((x2hA5 p).map (Int.cast : ℤ → ℂ)) y z = ((aEntT (x2hA5 p) y z : ℤ) : ℂ)
    simp only [aEntT, dif_pos hy', dif_pos hz']
    rfl
  · have hy' : (y : ℕ) < 11 := hy
    have hz' : (z : ℕ) < 11 := hz
    show ((x2hA6 p).map (Int.cast : ℤ → ℂ)) y z = ((aEntT (x2hA6 p) y z : ℤ) : ℂ)
    simp only [aEntT, dif_pos hy', dif_pos hz']
    rfl

/-- An entry of `ρ(p) J` for a frame matrix `J` with integer entries `e c j`. -/
theorem rhoG_mul_apply (τ : Fin 7 × Fin 7 × Fin 7) (p : Fin 120) {κ : Type*} (J : Matrix (HIdx τ) κ ℂ)
    (e : κ → ℕ → ℤ) (hJ : ∀ j c, J j c = ((e c (j : ℕ) : ℤ) : ℂ)) (i : HIdx τ) (c : κ) :
    (rhoG τ p * J) i c = ((∑ z0 ∈ Finset.range (hsz τ.1), ∑ z1 ∈ Finset.range (hsz τ.2.1),
      ∑ z2 ∈ Finset.range (hsz τ.2.2), aEnt τ.1 p (x2hE τ i).1 z0 * (aEnt τ.2.1 p (x2hE τ i).2.1 z1 *
        (aEnt τ.2.2 p (x2hE τ i).2.2 z2 * e c ((z0 * hsz τ.2.1 + z1) * hsz τ.2.2 + z2))) : ℤ) : ℂ) := by
  rw [Matrix.mul_apply, ← (x2hE τ).symm.sum_comp]
  simp only [rhoG, x2hTriple_apply, Equiv.apply_symm_apply, hJ, x2hE_symm_val, x2hAct_ent]
  simp only [Fintype.sum_prod_type, Finset.sum_range, Int.cast_sum, Int.cast_mul]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  apply Finset.sum_congr rfl; intro d _
  ring

/-- A passing `keyCheck b` gives the three transposition identities of the image of `b`. -/
theorem x2hTransp_ids_of_check (b : x2Key 0) (hk : keyCheck b = true) :
    rhoG (x2hTau b) (x2hSpecial 5) * x2hImage b = -x2hImage b ∧
    rhoG (x2hTau b) (x2hSpecial 10) * x2hImage b = -x2hImage b ∧
    (∑ u : Fin 10, rhoG (x2hTau b) (x2hSpecial u.succ.castSucc)) * x2hImage b = (2 : ℂ) • x2hImage b := by
  unfold keyCheck at hk
  have hcol : ∀ c : x2Col 0 b, colCheck 32 (x2hTau b).1 (x2hTau b).2.1 (x2hTau b).2.2 (hsz (x2hTau b).1)
      (hsz (x2hTau b).2.1) (hsz (x2hTau b).2.2) (x2JCols (x2KeyGlobal 0 b) c) = true :=
    fun c => List.all_eq_true.mp hk c (List.mem_range.mpr c.isLt)
  have hJ : ∀ (j : HIdx (x2hTau b)) (c : x2Col 0 b),
      x2hImage b j c = ((ent 11 10 (x2JCols (x2KeyGlobal 0 b) c) (j : ℕ) : ℤ) : ℂ) := fun j c => rfl
  have hent := fun (p : Fin 120) (i : HIdx (x2hTau b)) (c : x2Col 0 b) =>
    rhoG_mul_apply (x2hTau b) p (x2hImage b) (fun c k => ent 11 10 (x2JCols (x2KeyGlobal 0 b) c) k) hJ i c
  have hsnd := fun (i : HIdx (x2hTau b)) (c : x2Col 0 b) =>
    colCheck_sound (x2hTau b).1 (x2hTau b).2.1 (x2hTau b).2.2 (x2JCols (x2KeyGlobal 0 b) c) (hcol c)
      (x2hE _ i).1 (x2hE _ i).2.1 (x2hE _ i).2.2 (x2hE _ i).1.isLt (x2hE _ i).2.1.isLt (x2hE _ i).2.2.isLt
  refine ⟨?_, ?_, ?_⟩
  · ext i c
    rw [hent, (hsnd i c).1 5 (Or.inl rfl), x2hE_val, Matrix.neg_apply, hJ]
    simp
  · ext i c
    rw [hent, (hsnd i c).1 10 (Or.inr rfl), x2hE_val, Matrix.neg_apply, hJ]
    simp
  · ext i c
    rw [Matrix.sum_mul, Matrix.sum_apply]
    simp only [hent]
    rw [← Int.cast_sum, (hsnd i c).2, x2hE_val, Matrix.smul_apply, hJ, smul_eq_mul]
    simp

end ThreeCopyQutritWerner.X2Sites
