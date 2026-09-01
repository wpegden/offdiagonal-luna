# Process memory index

Kernel-generated; one line per ACTIVE entry. Full entries live in the
per-cone files. Do not hand-edit.

- [pm-0001-sampling-deletion-requires-positive-k] constraint/global — The paper's sampling/deletion lemma at paper/new.tex:415-429 assumes k >= 1. Tablet/SamplingDeletion.lean currently omits that premise, and Tablet/ThmMain.lean 
- [pm-0002-generic-coherent-tree-wrapper-is-not-the-old-lem] refuted-route/global — Tablet/OldCoherentTreeCount currently assumes an existential binary signature count with the same hypotheses and conclusion as RootedTreeCounting. Its G, t, and
- [pm-0003-retain-the-corrected-f2-nonedge-count] constraint/global — For p = s - 1, the old pair digraph uses nonedge pairs: x has 2^p - 1 nonzero choices and, for each x, exactly 2^(p-1) vectors y with dot(x,y) = 1. Thus its ord
