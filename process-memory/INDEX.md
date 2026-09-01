# Process memory index

Kernel-generated; one line per ACTIVE entry. Full entries live in the
per-cone files. Do not hand-edit.

- [pm-0001-sampling-deletion-requires-positive-k] constraint/global — The paper's sampling/deletion lemma at paper/new.tex:415-429 assumes k >= 1. Tablet/SamplingDeletion.lean currently omits that premise, and Tablet/ThmMain.lean 
- [pm-0002-generic-coherent-tree-wrapper-is-not-the-old-lem] refuted-route/global — Tablet/OldCoherentTreeCount currently assumes an existential binary signature count with the same hypotheses and conclusion as RootedTreeCounting. Its G, t, and
- [pm-0003-retain-the-corrected-f2-nonedge-count] constraint/global — For p = s - 1, the old pair digraph uses nonedge pairs: x has 2^p - 1 nonzero choices and, for each x, exactly 2^(p-1) vectors y with dot(x,y) = 1. Thus its ord
- [pm-0004-asymptotic-d-star-prose-is-not-a-tuple-count-pro] refuted-route/global — The high-level DStarCounting proof that only asserts |V(G)| ~ q^t, |V(D*)| ~ q^(2t-1), generic popular/poor children, and an O_t(q log q) unmarked path does not
- [pm-0005-reduce-arbitrary-delta-before-the-general-target] constraint/global — ThmOffDiagonalGeneral quantifies over every delta>0, but its current prose says it may assume 0<delta<1/10 without a reduction. The proof must set delta0=min(de
