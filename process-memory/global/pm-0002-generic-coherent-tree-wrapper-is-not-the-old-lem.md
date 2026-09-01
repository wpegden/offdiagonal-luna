---
id: pm-0002-generic-coherent-tree-wrapper-is-not-the-old-lem
type: refuted-route
status: active
coarse_node: global
created: {cycle: 11, request_id: 41}
---

Tablet/OldCoherentTreeCount currently assumes an existential binary signature count with the same hypotheses and conclusion as RootedTreeCounting. Its G, t, and q parameters do not encode the polarity construction, so it contributes no old-branch mathematics. The paper's substantive lemma at paper/new.tex:481-508 must be represented by the node itself or the node must be removed and the bound merged into OldPolarityConstruction.
