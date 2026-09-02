---
id: pm-0006-do-not-wrap-the-permutation-reduction
type: refuted-route
status: active
coarse_node: global
created: {cycle: 33, request_id: 107}
---

The current `RandomPermutationReduction` theorem already has the correct random construction, clique elimination, expectation estimate, and factorial bound. The recorded soundness rejection is specifically structural: its proof block omits an explicit `\noderef{CliqueWitness}` citation for the clique-witness invocation and an explicit `\noderef{TransitiveTournament}` citation for the ordered forbidden-tournament conclusion. A generic wrapper, helper, or theorem-signature change is unnecessary and does not repair the pinned defect; edit the existing proof block and preserve the contract.
