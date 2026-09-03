---
id: pm-0007-sampling-deletion-now-carries-positive-k-premise
type: constraint
status: active
coarse_node: global
created: {cycle: 55, request_id: 179}
---

The paper's sampling/deletion lemma at paper/new.tex:415-429 requires 1 <= k. That premise is now restored in Tablet/SamplingDeletion.lean as hk : 1 <= k and in Tablet/SamplingDeletion.tex in the lemma statement; ThmMain, ThmKCk, ThmClose, and ThmOffDiagonalGeneral explicitly establish it before invoking the lemma. Retain this constraint for all future Lean closure and never invoke SamplingDeletion at k = 0.
