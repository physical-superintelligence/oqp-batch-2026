module

public import ThreeCopyQutritWerner.CertificateX2HKeysKind

@[expose] public section


/-!
# The h images are injective

For every h key `b`, a set `R_b` of `r_b` rows and an integer matrix `K_b` with
`K_b J_b[R_b, :] = d_b I` (`d_b > 0`). `injCheck_sound`: a passing check makes
`(x2hImage b).mulVec` injective (an explicit left inverse). With the positive definite three-site
metric this gives the bridge's `metric_det` (CertificateX2SitesBridge-side assembly).
-/

set_option maxRecDepth 100000

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner.X2Sites

open X2

x2_nat_table hinvRows "verification/matrix-literals/x2-sites/hinv-rows.hex"
x2_nat_list hinvD "verification/matrix-literals/x2-sites/hinv-d.hex"
x2_nat_table hinvK "verification/matrix-literals/x2-sites/hinv-K.hex"
x2_nat_list hinvStart "verification/matrix-literals/x2-sites/hinv-start.hex"

/-- `∑_k (K_k - 2^100) · J_g[R_k, c]` over two lists. -/
noncomputable def dotKJ (g S c : ℕ) : List ℕ → List ℕ → ℤ
  | k :: ks, r :: rs => ((k : ℤ) - 2 ^ 100) * jEntry2 g S r c + dotKJ g S c ks rs
  | _, _ => 0

theorem dotKJ_eq (g S c : ℕ) : ∀ (Ks Rs : List ℕ), Ks.length = Rs.length →
    dotKJ g S c Ks Rs = ∑ k ∈ Finset.range Ks.length,
      ((Ks.getD k 0 : ℤ) - 2 ^ 100) * jEntry2 g S (Rs.getD k 0) c
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | k :: ks, r :: rs, h => by
    have h' : ks.length = rs.length := by simpa using h
    show ((k : ℤ) - 2 ^ 100) * jEntry2 g S r c + dotKJ g S c ks rs = _
    rw [dotKJ_eq g S c ks rs h', List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    ring

/-- The per-key kernel check of the left-inverse certificate. -/
noncomputable def injCheck (b : x2Key 0) : Bool :=
  let τ := x2hTau b
  let S := hsz τ.2.1 * hsz τ.2.2
  let r := x2KeySize 0 b
  let g := (x2KeyGlobal 0 b : ℕ)
  let R := hinvRows.getD b []
  let d := hinvD.getD b 0
  let st := hinvStart.getD b 0
  (R.length == r) && (R.all fun i => Nat.blt i (hsz τ.1 * S)) && Nat.blt 0 d &&
    (List.range r).all fun a =>
      ((hinvK.getD (st + a) []).length == r) && (List.range r).all fun c =>
        dotKJ g S c (hinvK.getD (st + a) []) R == (if a = c then (d : ℤ) else 0)

theorem injCheck_sound (b : x2Key 0) (h : injCheck b = true) :
    Function.Injective (x2hImage b).mulVec := by
  set τ := x2hTau b
  set S := hsz τ.2.1 * hsz τ.2.2
  set r := x2KeySize 0 b
  set g := (x2KeyGlobal 0 b : ℕ)
  set R := hinvRows.getD b []
  set d := hinvD.getD b 0
  set st := hinvStart.getD b 0
  unfold injCheck at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨hRl, hRb⟩, hd⟩, hK⟩ := h
  have hd0 : (d : ℂ) ≠ 0 := by
    have := Nat.blt_eq.mp hd
    exact_mod_cast (Nat.pos_iff_ne_zero.mp this)
  have hRlt : ∀ k : Fin r, R.getD k 0 < hsz τ.1 * S := by
    intro k
    have hk : (k : ℕ) < R.length := by rw [hRl]; exact k.isLt
    rw [List.getD_eq_getElem _ _ hk]
    exact Nat.blt_eq.mp (hRb _ (List.getElem_mem hk))
  -- the left inverse
  let L : Matrix (x2Col 0 b) (HIdx τ) ℂ := Matrix.of fun a i =>
    ∑ k : Fin r, if (i : ℕ) = R.getD k 0 then
      ((((hinvK.getD (st + a) []).getD k 0 : ℤ) - 2 ^ 100 : ℤ) : ℂ) / (d : ℂ) else 0
  have hLJ : L * x2hImage b = 1 := by
    ext a c
    obtain ⟨hKl, hKc⟩ := hK a a.isLt
    have hrow := hKc c c.isLt
    rw [dotKJ_eq g S c _ R (by rw [hKl, hRl])] at hrow
    rw [Matrix.mul_apply]
    simp only [L, Matrix.of_apply, Finset.sum_mul, ite_mul, zero_mul]
    rw [Finset.sum_comm]
    have hcol : ∀ k : Fin r, (∑ i : HIdx τ, if (i : ℕ) = R.getD k 0 then
        ((((hinvK.getD (st + a) []).getD k 0 : ℤ) - 2 ^ 100 : ℤ) : ℂ) / (d : ℂ) * x2hImage b i c else 0) =
        ((((hinvK.getD (st + a) []).getD k 0 : ℤ) - 2 ^ 100 : ℤ) : ℂ) / (d : ℂ) *
          ((jEntry2 g S (R.getD k 0) c : ℤ) : ℂ) := by
      intro k
      rw [Finset.sum_eq_single ⟨R.getD k 0, hRlt k⟩]
      · rw [if_pos rfl, x2hImage_apply]
      · intro i _ hi
        rw [if_neg]
        intro hc
        exact hi (Fin.ext hc)
      · intro hn
        exact absurd (Finset.mem_univ _) hn
    simp only [hcol]
    have hsum : ∑ k : Fin r, ((((hinvK.getD (st + a) []).getD k 0 : ℤ) - 2 ^ 100 : ℤ) : ℂ) / (d : ℂ) *
        ((jEntry2 g S (R.getD k 0) c : ℤ) : ℂ) =
        ((∑ k ∈ Finset.range (hinvK.getD (st + a) []).length,
          (((hinvK.getD (st + a) []).getD k 0 : ℤ) - 2 ^ 100) * jEntry2 g S (R.getD k 0) c : ℤ) : ℂ) / (d : ℂ) := by
      rw [hKl, ← Fin.sum_univ_eq_sum_range (fun k => (((hinvK.getD (st + a) []).getD k 0 : ℤ) - 2 ^ 100) *
        jEntry2 g S (R.getD k 0) c) r]
      push_cast
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [hsum, hrow]
    by_cases hac : (a : ℕ) = c
    · have hac' : a = c := Fin.ext hac
      rw [if_pos hac, hac', Matrix.one_apply_eq, Int.cast_natCast]
      exact div_self hd0
    · rw [if_neg hac, Matrix.one_apply_ne (fun h => hac (congrArg Fin.val h))]
      simp
  intro v w hvw
  have := congrArg (fun x => L.mulVec x) hvw
  simp only [Matrix.mulVec_mulVec, hLJ, Matrix.one_mulVec] at this
  exact this

end ThreeCopyQutritWerner.X2Sites
