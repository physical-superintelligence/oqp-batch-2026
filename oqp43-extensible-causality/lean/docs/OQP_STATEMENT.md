# Open Quantum Problem 43: the statement

**Source.** IQOQI Vienna, Open Quantum Problems, Problem 43, *Are all extensibly causal processes
purifiable?* Dated 22 May 2017 in the list of problems; contacts M. Araújo and Č. Brukner.
Page: <https://oqp.iqoqi.oeaw.ac.at/are-all-extensibly-causal-processes-purifiable>.

**Snapshot.** The text below is the section "Problem" of the archived copy of 29 October 2023,
<https://web.archive.org/web/20231029013446/https://oqp.iqoqi.oeaw.ac.at/are-all-extensibly-causal-processes-purifiable>,
reproduced verbatim, including its wording, spelling and punctuation; only the mathematical
notation has been put into LaTeX delimiters.

---

## Problem

The most general situation compatible with the assumption that the operations performed in each
local laboratory are described by the quantum formalism without assuming a global causal order
between the operations can be represented in the “process matrix” formalism [1]. The probability
that $N$ parties $A^1, ..., A^N$ observe the outcomes $a_1, ..., a_N$, for a choice of operations
$x_1, ..., x_N$ is a multilinear function of the corresponding CP maps
$\mathcal{M}_{a_1|x_1},...,\mathcal{M}_{a_N|x_N}$ as given by

$$p(\mathcal{M}_{a_1|x_1},...,\mathcal{M}_{a_N|x_N})= \mbox{Tr}[(M_{a_1|x_1} \otimes ... \otimes M_{a_N|x_N}) W],$$

where $M_{a_1|x_1}, ..., M_{a_N|x_N}$ are the CJ representations of the CP maps and
$W \in A^1_I \otimes A^1_O \otimes ... \otimes A^N_I \otimes A^N_O$ is a process matrix with $A^i_I$
and $A^i_O$ being the input and the output Hilbert spaces of party $i$. The set of process
matrices is defined by requiring that probabilities are well-defined [1,2].

The condition for a bipartite probability distribution to be “causal”, i.e., not to violate any
causal inequality, is that it can be decomposed into a convex combination of a probability
distribution which is no-signaling from Bob to Alice ($p^{A<B}$) and a probability distribution
which is no-signaling from Alice to Bob ($p^{B<A}$): $p_{causal} = \lambda p^{A<B} + (1 - \lambda) p^{B<A}$.
The generalization to arbitrary number of parties can be found in [2,3]. It is known that some
process matrices can violate causal inequalities[1,4], thought no physical implementation of such
processes are known. The processes are called *causal* if they do not violate causal
inequalities, and they are called *extensibly causal* if they remain causal even under extension
with input systems in an arbitrary joint quantum state [3].

The process matrices are called *pure* if after extending them with a global past state from the
Hilbert space $P$ and a global future state from the Hilbert space $F$, they induce a unitary
transformation from the past to the future whenever unitary transformations are also applied in
the local laboratories [5]. Then a process
$W \in P \otimes A^1_I \otimes A^1_O \otimes ... \otimes A^N_I \otimes A^N_O \otimes F$ is called
*purifiable* if one can recover it from a  pure process
$S \in P \otimes P' \otimes A^1_I \otimes A^1_O \otimes ... \otimes A^N_I \otimes A^N_O \otimes F \otimes F'$
by inputing the state $|0\rangle$ in $P'$ and tracing out the state from $F'$

$$W=\mbox{Tr}_{P'F'} [S^T (|0\rangle \langle 0|^{P'} \otimes \mathbb{I}^{F'})].$$

Here $P'$ and $F'$ are additional input and output Hilbert spaces of $S$ and $S^T$ is transposed
process $S$.

The question is whether or not any extensibly causal process is purifiable.

---

The page's section "Background" ends: "A negative answer would imply that either not all causal
processes are physical, or that purifiability is not a necessary condition for the physicality of
a process."

## References of the page

[1] O. Oreshkov, F. Costa, and C. Brukner, *Quantum correlations with no causal order*, Nature
Communications 3, 1092 (2012).

[2] M. Araújo, C. Branciard, F. Costa, A. Feix, C. Giarmatzi, and C. Brukner, *Witnessing causal
nonseparability*, New J. Phys. 17, 102001 (2015).

[3] O. Oreshkov and C. Giarmatzi, *Causal and causally separable processes*, New J. Phys. 18,
093020 (2016).

[4] C. Branciard, M. Araújo, F. Costa, A. Feix, and C. Brukner, *The simplest causal inequalities
and their violation*, New J. Phys. 18, 013008 (2016).

[5] M. Araújo, A. Feix, M. Navascués, and C. Brukner, *A purification postulate for quantum
mechanics with no causal order*, Quantum 1, 10 (2017). (Published as *A purification postulate
for quantum mechanics with indefinite causal order*.)

## Where each part of the statement is formalized

See [`FIDELITY.md`](FIDELITY.md).
