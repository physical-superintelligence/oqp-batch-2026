# Verification package — "Three copies of the Werner state: the sharp curve in dimensions three and four and a bound in every dimension"

Ian MacCormack (Physical Superintelligence (PSI), Cambridge, MA — ian@psi.inc) and Ning Bao (Northeastern University and
Brookhaven National Laboratory). Version of 23 October 2026.

The paper has two computer-verified inputs: Theorem 6.4, the exact rational identities of Zenodo record
23134454 (d = 3) and of github.com/GLiuax/d4-three-copy-werner (d = 4), and Theorem 7.2, our own dimension-uniform
certificate (`uniform/`, verified here from scratch). Those data are published and are
**not redistributed** here (the d = 4 repository states no licence). This package re-runs both published
verifiers on pinned copies, verifies a content digest of every tracked file first, and contains two control
scripts and our receipts. It is about 500 kB (the uniform certificate's rationals and the logs).

| path | what |
|---|---|
| `replay_d3.sh` | clones the d = 3 repository at commit `66cd2f9`, checks the SHA-256 digest of its 776 tracked files, runs `certificate/verify.py` (exact) and `check_controls.py` (negative controls). ~4 min, 2.5 GB |
| `replay_d4.sh` | clones the d = 4 repository at commit `2ba792f`, checks the digest of its 2510 tracked files, runs the five stages of `research/d4_independent_certificate_audit.py` (exact). ~7 min on two cores |
| `controls/control_d4.py` | independent floating-point control of the d = 4 certificate: builds the lift of an actual 64×64 matrix C, computes its averaged moments from the literal permutation operators, and evaluates the stored data on them (Sec. VIII of the paper). Needs the clone made by `replay_d4.sh` |
| `uniform/` | **the dimension-uniform certificate of Theorem 7.2** (Sec. VII of the paper): `certificate_uniform.json` (α₀ = 37/80, ε, the multiplier μ of the hand input T_B, and the rational coefficients y_{τ,p} on orbit representatives; ≈ 200 kB), the exact verifier `verify_uniform.py` and the five modules it uses (`diagrams.py` Brauer-diagram calculus with d as a parameter, `specht.py` rational Specht modules, `cellmod.py` the walled-Brauer blocks ρ_r(p;d), G_r(d), `kform.py` the determinant form K(w), `handcone.py` the hand-input tensors). `python3 -I uniform/verify_uniform.py uniform/certificate_uniform.json` recomputes everything but the stored rationals and performs checks (7)–(9) of Sec. VIII in exact arithmetic (~75 s, numpy only). `uniform/discovery/` holds the search that found the certificate (`sdp_setup.py` → `sdp_data.pkl` (170 MB, not shipped), `run_bisect.py`, `rationalize.py`; needs cvxpy + Clarabel; `bisection.log` and `final_solve.log` are its receipts); it is not part of the proof |
| `controls/uniform_hand_checks.py` | numerical checks of the hand identities of Sec. VII and Appendix B (determinant form and its permutations κ, the products T±, positivity of H_a for the hand weight vectors, every identity in the proof of Theorem B.1); not part of the proof |
| `controls/zero_census.py` | the numerical evidence of Remark 4.5(a),(b): random-start L-BFGS minimisation of q/‖C‖² with the analytic gradient, classification of every converged zero into families I–III (local supports + normal form), and Hessian nullities at one sampled point per family. `python3 -I controls/zero_census.py 3 500 0` and `... 4 200 0` reproduce the counts in the paper (seeds 0; ~15 s and ~30 s) |
| `controls/hand_identities.py` | checks the hand identities of the paper (Prop. 3.1, Thm. 1.2's value, Prop. 2.1, Lemma 2.4, Remark 3.2(a), Prop. 4.2(a), Remark 4.3, (A1)–(A3)) symbolically or numerically; not part of the proof |
| `receipts/` | logs of our runs (Linux, Python 3.13, two cores); `replay_d3.log` keeps the per-block lines |
| `SHA256SUMS` | hashes of every file in this package |

## Requirements

`git`; Python ≥ 3.11 with `numpy`, `scipy`, `sympy`, `mpmath`, `python-flint` (≥ 0.6) and, for `control_d4.py`
only, `opt_einsum`. Network is needed only for the two `git clone`s.

    pip install numpy scipy sympy mpmath python-flint opt_einsum

## Expected results

    bash replay_d3.sh
    # content digest matches (776 tracked files); last JSON line of the verifier:
    # "status": "COMPLETE_PORTABLE_EXACT_CERTIFICATE_PASS", "exact_functional_equations": 2374,
    # "nonzero_PSD_multipliers": 716; then SEMANTIC_NEGATIVE_CONTROLS_PASS        (receipts/replay_d3.log)

    bash replay_d4.sh
    # content digest matches (2510 tracked files); five stages exit 0; the certificate stage prints
    # {"coefficient_identities": 2741, "positive_Gram_blocks": 1239, "positive_congruence_rows": 4231,
    #  "rational_margin_lower_bound": "9999992/10000000", "all_exact": true, ...}  (receipts/replay_d4.log)

    python3 -I controls/control_d4.py upstream_d4/research/matched_d4 random 1
    python3 -I controls/control_d4.py upstream_d4/research/matched_d4 zero 3
    # c^T xi = q(C) to 1e-15, |K xi| ~ 1e-14, all 1239 compressions PSD (~ -1e-14), identity diff ~ 1e-16;
    # at the exact zero every compression vanishes                          (receipts/control_d4_*.log)

    python3 -I controls/hand_identities.py
    # ALL CHECKS PASSED                                                      (receipts/hand_identities.log)

    python3 -I uniform/verify_uniform.py uniform/certificate_uniform.json
    # (1) coefficient identity holds ... (2)(3) tau = ... 35/56 leading blocks > eps I ...
    # ALL CHECKS PASSED: 343 blocks; Q_alpha0(X) >= 0 for every rank-<=2 X in every dimension, alpha0 = 37/80
    #                                                            (receipts/verify_uniform.log)

    python3 -I controls/uniform_hand_checks.py
    # ALL HAND CHECKS PASSED                                      (receipts/uniform_hand_checks.log)

    python3 -I controls/zero_census.py 3 500 0 ;  python3 -I controls/zero_census.py 4 200 0
    # d=3: {'I': 74, 'II': 6, 'III': 420, 'other': 0, 'unconverged': 0}; Hessian nullities 46, 34, 46
    # d=4: {'I': 82, 'II': 7, 'III': 111, 'other': 0, 'unconverged': 0}; Hessian nullities 78, 46, 58
    #                                                   (receipts/zero_census_d3.log, zero_census_d4.log)

(`control_d4.py` uses the upstream variable names: x for the coordinate vector ξ, E for the relation matrix K,
Z_t for the blocks G_t, M_t for the compressions Ŷ_t.)

## Interface between the paper (Sec. VII) and `uniform/certificate_uniform.json`

`alpha0` = 37/80; `epsilon` = 243444/653071328197; `mu` = {"det lemma2": μ} is the multiplier of T_B = det H_{a_B}
(eq. (23), Theorem B.1; "lemma2" is the internal name of that bound); `y["(τ)"]` maps an orbit representative monomial `p1|p2|p3` (each p_i a permutation of
0123 written as p(0)p(1)p(2)p(3), replicas (u0,v0,u1,v1) = (0,1,2,3), P_p sends input position j to output position
p(j)) to the rational coefficient y_{τ,p} of ⊗_i P_{p_i} in Y_τ; the orbit is under site permutations × V4 relabellings
× adjoint for τ = (), (0,1), (0,2), (0,3) and under site permutations × adjoint for τ = (0,). Y_{{j}} = g_j Y_{{0}} g_j⁻¹.
The ideal E is K(α₀) − μT_B − ΣY_τ (recomputed, not stored). Transpose set τ = replicas conjugated; the walled
Brauer diagrams, cell modules (half-diagrams × polytabloids), representation matrices ρ_r(p;d), contravariant forms
G_r(d), their leading coefficients and the 238 (+105 relabelled) leading blocks B̄_{τ,r}(0) are all recomputed by
the verifier from `cellmod.py`.

## Interface between the paper (Sec. VI) and the stored certificate data

The verifiers check the stored data; the correspondence below says which stored object each object of Sec. VI is.
Upstream names in `code`. The d = 3 data are in `certificate/` of the Zenodo repository (paper `paper.md`,
Secs. 1–5 and eqs. (14)–(28) there); the d = 4 data in `research/matched_d4/` of the Liu repository.

| paper object | d = 3 (Zenodo 23134454) | d = 4 (Liu, `research/matched_d4`) |
|---|---|---|
| coordinate vector ξ (sectors 31, 22, 13) | basis-coordinate column `X` of the *scaled* moments X_f = L·Y_f, L = 54⁴ (eq. 14), on the projected permutation-word bases of `data/basis_data.npz` (`basis31_indices`, …; 577 + 1220 + 577) | coordinates `x` on the orbit bases `diagrams_31/22/13.npz` (667 + 1407 + 667), moments scaled by `normalization` = 128⁴ in `source.json` |
| objective c, with c^Tξ = q(C) for ‖C‖² = ½ | `global_objective_numerator/denominator` in `basis_data.npz`; c(X) = L⁻¹ Tr[Z_{0,3} X_31] = q₃(C) (eq. 15) | `objective` in `source.json`; `control_d4.py` checks c^T x = q₃(C) to 1e-15 |
| relation matrix K and selected rows K₀, multiplier η | `E` (2912 × 2374, denominator 1152): the three conditional (isometry) contrasts followed by the signed AAB and ABB marginal differences; K₀ = `B` = 1152·E_{I,:} (272 rows, `equality_basis_rows`), η in `data/equality_multiplier.json` (λ_I = 1152η, eq. 28) | `equality_integer.npz` (2912 × 2741) and the 272 selected rows and η in `full_gram_crossed/rational_certificate/` |
| compressions Ŷ_t(ξ) = N_tᵀ J_tᵀ M_t(ξ) J_t N_t | word, cut and modules of block t in `multipliers/<t>.json` (`family`, `cut`, `modules`); the rational embedding J_t and the metric J_tᵀJ_t per local module in `data/local_modules.json` (upstream calls this metric G_t; it is *not* the paper's G_t) (eqs. 23–24a: metric · π_t(X) = J_tᵀ X J_t); frame `N` in `multipliers/<t>.json` (eq. 25: D_t = N Z Nᵀ, ℓ_t = Tr[D_t G_t π_t(X)]) | maps M_t(x) in `full_gram_crossed/rational_maps/<t>.npz` (1239 files); frames in `full_gram_crossed/frames.json`, `exact_frames.json` |
| positive blocks G_t (paper) = `Z` (upstream); G_t acts on the reduced carrier selected by N_t, and positivity is asserted there, never on the full isotypic block | `Z` in `multipliers/<t>.json` (716 files; positivity by the characteristic-polynomial sign test) | `full_gram_crossed/rational_certificate/<t>.json` (1239; positivity by rational congruence to a diagonally dominant matrix, `positive_blocks.json`) |
| coupled block (paper eq. (14), u ⊕ v) | Sec. 3.2, eqs. (17)–(20): diagonal blocks (V_τ Y_31 V_τ*)^{Γ_{3}}, (V_τ Y_13 V_τ*)^{Γ_{3}} with τ = (2 3); off-diagonal block the index rule (19); cross contribution 2 Tr[D_21 G_t π_t(B(X_22))] (eq. 27); the 64 blocks with `kind` = joint | the 111 `crossed` blocks of `full_gram_crossed` |

In the paper's notation the certificate identity (16) reads c^Tξ = Σ_t Tr[Z_t N_tᵀ J_tᵀ M_t(ξ) J_t N_t] + ηᵀK₀ξ; upstream
writes the same identity as c = Σ_t ℓ_t + Eᵀλ (Zenodo eq. 28) and as c^T x = Σ_t Tr[Z_t M_t(x)] + ηᵀE₀x (Liu).

## What is and is not verified

Verified in exact arithmetic by the upstream verifiers: items (1)–(6) of Sec. VIII of the paper; by `uniform/verify_uniform.py`: items (7)–(9). Not verified by
any program: the hand proofs, the interpreters, the hardware. The floating-point semidefinite programs that
discovered the certificates are not needed.

## Attribution

d = 3: Anonymous, Zenodo record 10.5281/zenodo.23134454 (CC0-1.0 data, MIT code), fetched from the mirror
github.com/ipitchford/three-copy-werner-undistillability. d = 4: A.-X. Liu, github.com/GLiuax/d4-three-copy-werner,
commit 2ba792f (cited, not redistributed). Scripts, controls and receipts: the authors of the paper.

## Licence

Code (`*.py`, `*.sh`) is released under the MIT licence; data, logs and documentation (`*.json`, `*.log`, `*.md`,
`SHA256SUMS`) under CC BY 4.0. See `../LICENSE.md`. The two published certificates are not redistributed (see Attribution).
