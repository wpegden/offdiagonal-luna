---
id: pm-0003-retain-the-corrected-f2-nonedge-count
type: constraint
status: active
coarse_node: global
created: {cycle: 11, request_id: 41}
---

For p = s - 1, the old pair digraph uses nonedge pairs: x has 2^p - 1 nonzero choices and, for each x, exactly 2^(p-1) vectors y with dot(x,y) = 1. Thus its order is (2^p - 1)2^(p-1) = 2^(2s-3) - 2^(s-2). The formula (2^p - 1)(2^(p-1) - 1) printed in paper/new.tex:640-646 counts orthogonal ordered pairs instead. Keep the Tablet's corrected formula and explicitly ground this source correction.
