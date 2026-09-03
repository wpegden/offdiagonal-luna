---
id: pm-0001-sampling-deletion-requires-positive-k
type: constraint
status: superseded
superseded_by: pm-0007-sampling-deletion-now-carries-positive-k-premise
coarse_node: global
created: {cycle: 11, request_id: 41}
---

The paper's sampling/deletion lemma at paper/new.tex:415-429 assumes k >= 1. Tablet/SamplingDeletion.lean currently omits that premise, and Tablet/ThmMain.lean and Tablet/ThmKCk.lean invoke it at k = 0, deriving contradictions. The missing hk : 1 <= k must be restored before any target body is treated as a valid proof.
