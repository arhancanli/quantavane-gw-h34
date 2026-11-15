# Notes: what is proved and how it was checked (15 November 2026)

## What is proved

Everything below is proved in Lean 4 (v4.35.0, Mathlib v4.35.0) with no `sorry`, no `native_decide`
and only the axioms `propext`, `Classical.choice` and `Quot.sound`. The statements of record are in
`Challenge.lean`; `comparator.json` names the four compared theorems.

- `GwH34.no_good_53`: for every type `α` and every `c : ℕ → α`, `¬ IsGood 4 53 c`.
- `GwH34.no_good_of_le`: the same for `[1, n]`, `n ≥ 53`.
- `GwH34.exists_good_52`: a `(3, 4)`-good colouring of `[1, 52]` by natural numbers.
- `GwH34.H_four`: `H 4 = 53`.

The upper bound rests on `GwH34.cert_ok : checkH 53 cert = true`, proved by `decide +kernel`: Lean's
kernel runs the bitmask RUP checker over the 702 derived clauses of CaDiCaL's LRAT refutation that the
empty clause needs (20,963 hints: 18,473 to original clauses, named by descriptors, and 2,490 to
derived clauses). `scripts/make_cert.py` rebuilt the CNF in `gw_eq.py`'s order (replaying pysat's
variable numbering) and found its SHA-256 equal to that of the refuted file
(`9008c69718bda8d6999185b7ef4f71c4b64390fa0c5c13b8e13dfd86ab760e40`), checked every descriptor
against its clause, and renamed the variables to the atoms `64 i + j`; the LRAT file's SHA-256 is
`a7a1c1e1a19ce01b11631a101d1c48bb25732a78b1d1f836db1de295b0e82316`. Neither check is trusted:
`run_sound` and `descCls_holds` hold for every input.

## Line counts

| File | Lines |
|---|---|
| `Challenge.lean` | 70 (3,635 bytes) |
| `Solution.lean` | 40 |
| `GwH34.lean` | 8 |
| `GwH34/Defs.lean` | 31 |
| `GwH34/Check.lean` | 391 |
| `GwH34/Clauses.lean` | 220 |
| `GwH34/Cert.lean` | 726 (167,410 bytes; generated) |
| `GwH34/Lower.lean` | 60 |
| `GwH34/Upper.lean` | 23 |
| `scripts/CheckAxioms.lean` | 16 |

Every `.lean` file starts with `module`; `Challenge.lean` imports only Mathlib
(`Mathlib.Order.Lattice.Nat`).

## Checks run (Mac, Apple silicon, Lean v4.35.0)

All on a fresh clone of commit `3aedc2f0bc177cff2ae9edc7f5182f851a9efb17` (the commit before this
file was added; no Lean file changed since), with the Lake packages of the pinned Mathlib checkout and
the project's own modules built from scratch (a local check script; its log is kept outside this
repository).

1. `lake build`: every module built in 27 s; `GwH34.Upper` (the kernel check of the certificate) 9 s,
   `GwH34.Lower` 2 s. `Challenge` warns four times (declaration uses `sorry`, as intended).
2. `lake env lean scripts/CheckAxioms.lean`: `[propext, Classical.choice, Quot.sound]` for
   `no_good_53`, `no_good_of_le` and `H_four`; `[propext, Quot.sound]` for `exists_good_52`.
3. `lake comparator` needs bubblewrap (Linux namespaces) and does not run on macOS. In its place,
   steps 4 and 6 were run by hand.
4. Statement comparison: every constant reachable from the types of the compared theorems (following
   definition values, not proofs) was printed with `pp.all` and hashes in the Challenge and in the
   Solution environment. Apart from the module of the two own definitions (`Challenge` against
   `GwH34.Defs`), the two outputs (4 roots, 117 constants) are identical.
5. Red controls (`RedControl.lean`): the certificate against `[1, 52]`, without its last step, and
   with one hint bit flipped in its last step; the colouring of `[1, 52]` on `[1, 53]`, and tested for
   monochromatic 3-term progressions: all rejected by the kernel. The true certificate passes.
6. Kernel replays: `leanexport` wrote both modules with the compared theorems as targets; the Solution
   export (9.1 MB) was replayed through every kernel bundled with the toolchain (each run would have
   been stopped had it passed 7 GB of memory; none did):

   ```
   leanchecker            rc 0     7 s   1.1 GB
   nanoda                 rc 0     6 s   2.0 GB
   con-ron                rc 0     6 s   1.8 GB   accepted 2229 declarations (--verified)
   leanchecker-paranoid   rc 0    11 s   1.3 GB
   lean4lean              rc 0    10 s   1.1 GB   checked 2226 declarations
   con-leche              rc 0   240 s   1.3 GB   accepted 2229 declarations (--verified)
   ```

   NanoDa with unpermitted axioms as a hard error: Solution export exit 0; Challenge export exit 1
   (`export file declares unpermitted axiom "sorryAx"`), as it should. `Lean.ofReduceBool` does not
   occur in the Solution export. SHA-256 of the exports: `solution.ndjson`
   `845bed68b3f2159812cd055f73ea9fd3af0726499f8cea254c5b0c441fc855eb`, `challenge.ndjson`
   `9be4960b4fc97c717510827fe19332b98c938b36ca845aaf063e55c7f5dd04ac`.

## What remains

- Palomar's mechanical preflight (the workflow above, on GitHub's Linux runners) has not run: it needs
  the repository to be public on GitHub.
- No review outside Quantavane's agents.
- Not formalized: the consequences for `GW(r; 3, 4)` and `GW'(r; 3, 4)` named in the README; the other
  values of the paper (`H(3, 5) = 294`, `H(4, 3) = 57`), whose refutations are far larger (about
  10^5 to 10^6 proof steps).
