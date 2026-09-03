# Formalization of "Off-diagonal Ramsey numbers"

## Formalization by Trellis

## Paper targets

| Label | Node | Statement |
|---|---|---|
| `thm:close` | `Tablet.ThmClose` | Let $s\to\infty$ through positive integers and let $a\geq0$ be an integer sequence with $a=o(s)$. In the standard eventual sense, for every $\varepsilon>0$ and all sufficiently large indices, \[ r(s,s+a)\geq(1-\varepsilon)\frac{s}{e} 2^{(s+a-1)/2-a^2/(2s)}. \] Equivalently, this is \[ r(s,s+a)\geq(1+o(1))\frac{s}{e} 2^{(s+a-1)/2-a^2/(2s)}. \] |
| `thm:k-Ck` | `Tablet.ThmKCk` | Let $C>1$ be fixed. Interpret the paper's integer $Cs$ as $k_s=\lceil Cs\rceil$. Then, for all sufficiently large $s$, \[ r(s,k_s)\geq\left(2^{1-1/(2C)}\right)^s. \] The ceiling changes only a bounded rounding error and is the precise integer convention used here. |
| `thm:main` | `Tablet.ThmMain` | For any $s\geq3$, there is a positive constant $c_s$ such that for every $k\geq2$, \[ r(s,k)\geq c_s\frac{k^{s-1}}{(\log k)^{2s-4}}. \] |
| `thm:multicolor` | `Tablet.ThmMulticolor` | For every fixed integer $\ell\geq3$, \[ r(s;\ell)=\Omega\!\left(2^{(\ell-1)s/2}\right). \] That is, there are constants $c_\ell>0$ and $S_\ell$ such that the displayed lower bound with factor $c_\ell$ holds for every $s\geq S_\ell$. |
| `thm:off-diagonal-general` | `Tablet.ThmOffDiagonalGeneral` | For every $\delta>0$, there is a constant $L$ such that for all positive integers $s\geq L$ and $k\geq Ls$, \[ r(s,k)\geq\left(\frac{k}{s}\right)^{(1-\delta)s}. \] |

All 5 paper targets are Lean-closed against the pinned Mathlib revision, contain
no `sorry`, and depend only on the standard Lean axioms `propext`,
`Classical.choice` and `Quot.sound`. The project's axiom gate
(`APPROVED_AXIOMS.json`) authorizes no additional axioms. This holds of the whole
development, not only the targets: no node in `Tablet/` contains a `sorry`, and
none depends on `sorryAx`.

## Provenance

One commit per state-changing supervisor checkpoint — 68 commits.
The run was driven end to end by Trellis: a single model (OpenAI gpt-5.6-luna via the Codex CLI, reasoning effort "high") filled every
role — worker, reviewer, and the independent verifier lanes — with workers running
in a `bwrap` sandbox against a pinned Mathlib, and only the `Mathlib` import prefix
permitted.

The only human input was approval of the stated theorem statements at the human gate
after the theorem-stating phase. No mathematical content, proof steps, or
formalization hints were supplied by hand.

## Building

```
lake exe cache get
lake build
```

Requires the toolchain in `lean-toolchain` and the Mathlib revision pinned in
`lake-manifest.json`.
