---
id: pm-0005-reduce-arbitrary-delta-before-the-general-target
type: constraint
status: active
coarse_node: global
created: {cycle: 23, request_id: 80}
---

ThmOffDiagonalGeneral quantifies over every delta>0, but its current prose says it may assume 0<delta<1/10 without a reduction. The proof must set delta0=min(delta,1/20) or split cases, apply OldPolarityConstruction at delta0, and compare exponents using k/s>=1; it may not silently restrict the theorem's quantified delta. This correction is independent of the already accepted OldPolarityConstruction statement.
