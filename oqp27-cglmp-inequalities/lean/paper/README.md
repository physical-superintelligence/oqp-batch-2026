# Manuscripts and formalized statements

## Current manuscript

*The optimal CGLMP measurements on maximally entangled states*, draft of
21 October 2026, states the projective-measurement bound and equality
classification for Problem 27.B.

| Current manuscript result | Declaration in the formalization |
| --- | --- |
| Theorem 1, “Value and rigidity” (`thm:main`): local dimension equals the number of outcomes | `OQP27.partB_maximizers_are_fourier_phase`, specialized to `n = d` |
| Theorem 3, “General local dimension” (`thm:general`): arbitrary local dimension, with equality exactly for Fourier-phase measurements with a multiplicity | `OQP27.partB_maximizers_are_fourier_phase` |
| Fourier-phase attainment and the local CGLMP bound | `OQP27.fourier_attains_cglmp_value`, `OQP27.cglmp_local_bound` |
| Discussion: fixed CGLMP-witness threshold under uniform behaviour noise | `OQP27.cglmp_witness_tolerance` |

The declarations are in [Challenge.lean](../Challenge.lean) and
[Solution.lean](../Solution.lean).

## Source labels used by the formalization

The bibliographic source in [CITATION.cff](../CITATION.cff) is
*CGLMP optimality and the strength of Bell tests*, an October 2026 Letter with
supplementary material. The formalization uses the following labels from that
manuscript:

| Source label | Declaration or group |
| --- | --- |
| Theorem A.1 | `OQP27.partB_maximizers_are_fourier_phase`, `OQP27.fourier_attains_cglmp_value` |
| (B.1), (B.2), Appendix B | `OQP27.cglmp_local_bound`, `OQP27.fourier_projectors_pvm`, `OQP27.tracial_table_physical` |
| (A.5) | `OQP27.cglmp_witness_tolerance` |
| (A.6): tensor-CHSH noise comparison for `m ≥ 955` | `OQP27.noise_separation_955`, `OQP27.partB_noise_resistance_not_optimal` |
| Appendix F.2 | `OQP27.tensor_chsh_rank_one_pvm` |
| (F.16): statistical-strength comparison for `m ≥ 41` | `OQP27.statistical_separation`, `OQP27.partB_kl_discrimination_not_optimal` |
| Proposition G.1 | `OQP27.bgp_facet`, `OQP27.bgp_relative_interior_point`, `OQP27.bgp_no_signalling_violation`, `OQP27.bgp_not_cglmp_four`, `OQP27.bgp_no_fusion` |

The [problem-to-statement map](../docs/FIDELITY.md) gives the definitions and
assumptions for these results.
