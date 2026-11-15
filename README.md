# The canonical Gallai–van der Waerden number H(3, 4) = 53

A Lean 4 proof, with Mathlib, that every colouring of `{1, …, 53}`, with any number of colours,
contains a rainbow 3-term or a monochromatic 4-term arithmetic progression, while some colouring of
`{1, …, 52}` contains neither. So the canonical Gallai–van der Waerden number `H(3, 4)` is 53. It is
laid out for registration on [Palomar](https://palomar-registry.org): `Challenge.lean` states the
results, `Solution.lean` proves them, and `comparator.json` names the compared theorems.

## The result

Write `[1, n] = {1, …, n}`. An arithmetic progression (AP) has common difference at least 1. Under a
colouring, a progression is rainbow when its terms have pairwise distinct colours and monochromatic
when they all have one colour. For `k, l ≥ 2`, `H(k, l)` is the least `N` such that every colouring of
`[1, N]`, with any number of colours, contains a rainbow `k`-term AP or a monochromatic `l`-term AP.
It exists by the canonical van der Waerden theorem of Erdős and Graham. In terms of the
Gallai–van der Waerden numbers of Mao, Ozeki, Robertson and Wang (MORW; J. Combin. Theory Ser. A 193
(2023) 105672), `H(k, l)` is the largest of the non-exact numbers `GW'(r; k, l)` over all `r`.

**Theorem.** `H(3, 4) = 53`. More precisely:

1. every colouring of `[1, 53]`, with colours in any type, has a rainbow 3-term AP or a monochromatic
   4-term AP, and so has every colouring of `[1, n]` with `n ≥ 53`;
2. the 3-colouring `0221211122111212202212111221112122022121112211121222` of `[1, 52]` has neither.

## What is compared (`comparator.json`)

All four theorems are stated in `Challenge.lean` (with `sorry`) and proved in `Solution.lean`.

| Lean name | What it says |
|---|---|
| `GwH34.no_good_53` | For every type `α` and every `c : ℕ → α`, `¬ IsGood 4 53 c`. |
| `GwH34.no_good_of_le` | The same for `[1, n]` with `53 ≤ n`. |
| `GwH34.exists_good_52` | There is `c : ℕ → ℕ` with `IsGood 4 52 c`. |
| `GwH34.H_four` | `H 4 = 53`. |

`definition_names` is empty on purpose. The two definitions the statements use are spelled out in
full in `Challenge.lean`; Comparator follows them from the theorem statements and requires them to be
identical in the Solution, which takes them from `GwH34/Defs.lean`.

## Definitions

- `IsGood l n c` (for `c : ℕ → α`, any type `α`): no `x, x + d, x + 2d` in `[1, n]` with `d ≥ 1` has
  three distinct colours, and no `x, x + d, …, x + (l - 1)d` in `[1, n]` with `d ≥ 1` is
  monochromatic. Only the values of `c` on `[1, n]` matter.
- `H l := sInf {N | ∀ c : ℕ → ℕ, ¬ IsGood l N c}`: the least `N` such that no colouring of `[1, N]` by
  natural numbers is good. Colourings by natural numbers already allow any number of colours on a
  finite interval; `no_good_53` is stated for colours in any type. In Lean the infimum of the empty
  set of natural numbers is `0`; here the set contains 53.

## How the proof goes

**Lower bound** (`GwH34/Lower.lean`). The 3-colouring above (the one of the registered entry
PALOMAR-2026-11-13-000005 for `GW(3; 3, 4) = 53`) is stored as a natural number in base 8 and checked
by `decide +kernel` through a Boolean test proved sound in Lean (`isGood_of_goodB`).

**Upper bound** (`GwH34/Check.lean`, `Clauses.lean`, `Cert.lean`, `Upper.lean`). The statement "no
colouring of `[1, 53]` is good" is reduced to the unsatisfiability of a propositional formula (CNF)
in which colourings are described by equalities, so that the number of colours is not bounded, and
the unsatisfiability is checked in Lean's kernel from a solver certificate.

- *The CNF.* For each pair of positions `i < j` (the points `i + 1`, `j + 1`), an atom
  `e(i, j) = 64 i + j` says that the two points have the same colour. The clauses: transitivity for
  every triple of positions (three clauses each); for every 3-term AP, two of its terms have the same
  colour; for every 4-term AP, two consecutive terms have different colours. This is Quantavane's
  formula `gw_eq.py 53 4 0` (1,378 variables, 71,396 clauses), with its variables renamed.
- *The bridge* (`Clauses.lean`, `descCls_holds`). For a good colouring `c`, the assignment
  `e(i, j) := (c (i + 1) = c (j + 1))` satisfies every clause. No renaming of colours is needed, and
  the colours may lie in any type.
- *The certificate* (`Cert.lean`). CaDiCaL 3.0.1 refuted the CNF and wrote an LRAT proof; the 702
  derived clauses that the empty clause needs (of 1,211) are kept, with 20,963 hints.
  `scripts/make_cert.py` rebuilds the CNF in the order of `gw_eq.py`, checks its SHA-256 against the
  refuted file, names each original clause by a short descriptor (kind and parameters), renames the
  variables, and writes one natural number per derived clause.
- *The checker* (`Check.lean`). The bitmask RUP checker of PALOMAR-2026-11-13-000005 (`GwExact.Check`),
  with 13-bit literals and 16-bit counts: clauses are pairs of bitmasks, unit propagation is a few
  operations on natural numbers that the kernel performs with GMP, `descCls` recomputes an original
  clause from its descriptor, and derived clauses are kept in a binary trie. `run_sound` proves, for
  every input, that if all clauses the checker uses are true under an assignment then no run
  succeeds; so the certificate is untrusted data.
- *The kernel check* (`Upper.lean`). `cert_ok : checkH 53 cert = true` is proved by `decide +kernel`
  (about ten seconds).

**The value** (`Solution.lean`). A good colouring of `[1, n]` is good on every `[1, m]` with `m ≤ n`
(`isGood_mono`), so 53 is the least `N` with no good colouring.

No `sorry` outside `Challenge.lean`, no `native_decide`, no extra axioms:
`lake env lean scripts/CheckAxioms.lean` prints `[propext, Classical.choice, Quot.sound]` (or a
subset) for each compared theorem.

## Why it is of interest

Canonical van der Waerden numbers go back to Erdős and Graham, who asked how fast `H(k) = H(k, k)`
grows (Problem #190 of the Erdős problems database, answered recently by Bae and by Fox and Hunter).
Exact values are rare: as far as we know, the only exact value with `k, l ≥ 3` known before was
`H(3, 3) = 9`, which follows from the values of `GW(r; 3, 3)` (MORW; Y. Si, arXiv:2610.30711).
`H(3, 4) = 53` is, as far as we know, the second. It also gives `GW'(r; 3, 4) ≤ 53` and
`GW(r; 3, 4) ≤ max(53, r)` for every number of colours `r`. The natural readers are researchers in
Ramsey theory on the integers: van der Waerden numbers, rainbow (anti-van der Waerden) problems and
Gallai–Ramsey colourings.

## Provenance, literature and novelty

The value was obtained by Quantavane's computer search on 11 November 2026. Its statement is first
presented in this repository; Quantavane's paper "Power-residue colourings and exact
Gallai–van der Waerden numbers" (A. Canli, November 2026, not yet published) has it as Corollary 1.2,
and the formula and its LRAT proof are in the public data repository
[arhancanli/quantavane-gw-data](https://github.com/arhancanli/quantavane-gw-data) (public since
15 November 2026; `cnf/gw_any_53_l4.cnf` and `lrat/gw_any_53_l4.lrat` in `gw/certificates.tar.xz`), where
they serve as a confirmation of the row `GW(r; 3, 4)`. A literature search on 11 and 12 November 2026
(MORW; Si's arXiv paper; MathWorld; arXiv, Zenodo, GitHub, OEIS, Crossref and the Palomar registry)
found no published value of `H(3, 4)`. The search was limited to these sources, so novelty is our
reading of it, not an established fact.

## Authorship and the role of AI

Author and maintainer: Arhan Canli (Quantavane), who takes responsibility for the result.

The computer search, the encoding, the certificate checker, its soundness proof and every line of
Lean here were produced by AI agents (Claude, by Anthropic) working for Quantavane under Arhan Canli's
direction. No mathematician outside Quantavane has reviewed the proof.

## Checking it

Lean `v4.35.0` (`lean-toolchain`) and Mathlib `v4.35.0`
(`56a005855ea17e0b0958f73ec801ae140b0a1679`, pinned in `lake-manifest.json`).

```sh
lake exe cache get        # prebuilt Mathlib
lake build                # GwH34, Challenge, Solution (the kernel checks take about ten seconds)
lake env lean scripts/CheckAxioms.lean
lake comparator           # Linux with bubblewrap: compares Challenge and Solution and replays the proofs
python3 scripts/make_cert.py gw_any_53_l4.cnf gw_any_53_l4.lrat GwH34/Cert.lean   # regenerates Cert.lean
```

`.github/workflows/palomar-preflight.yml` runs Palomar's own mechanical check
(`PalomarRegistry/PalomarSubmission`, pinned commit) on every push to `main`.

## Files

- `Challenge.lean`: the statement of record (Mathlib imports only).
- `Solution.lean`: the four compared theorems with proofs.
- `GwH34/Defs.lean`: the two definitions, identical to those in `Challenge.lean`.
- `GwH34/Check.lean`: the bitmask RUP checker and its soundness (Lean core only).
- `GwH34/Clauses.lean`: the clauses from descriptors and their truth for a good colouring.
- `GwH34/Cert.lean`: the certificate (generated by `scripts/make_cert.py`).
- `GwH34/Upper.lean`, `GwH34/Lower.lean`: the two bounds.
- `comparator.json`, `formalization.yaml`, `scripts/CheckAxioms.lean`, `scripts/make_cert.py`.

## Licence

Apache-2.0 (`LICENSE`).
