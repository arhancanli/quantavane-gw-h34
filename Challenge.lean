module

public import Mathlib.Order.Lattice.Nat

@[expose] public section

/-!
# The canonical Gallai–van der Waerden number `H(3, 4) = 53`: the statement

This file is the statement of record. It imports only Mathlib, defines the notions the statements
use, and states the results with `sorry`. `Solution.lean` proves every statement; `comparator.json`
names the compared theorems. The definitions below must agree exactly with the ones the proof uses
(Comparator checks this), so they are spelled out here in full.

## Canonical van der Waerden numbers

Write `[1, n] = {1, …, n}`. An arithmetic progression (AP) always has common difference `d ≥ 1`.
Under a colouring, a progression is *rainbow* if its terms have pairwise distinct colours and
*monochromatic* if they all have the same colour. For `k, l ≥ 2`, the canonical (Gallai–)van der
Waerden number `H(k, l)` is the least `N` such that every colouring of `[1, N]`, with any number of
colours, contains a rainbow `k`-term AP or a monochromatic `l`-term AP. It exists by the canonical
van der Waerden theorem of Erdős and Graham. In terms of the Gallai–van der Waerden numbers of Mao,
Ozeki, Robertson and Wang (J. Combin. Theory Ser. A 193 (2023) 105672), `H(k, l)` is the largest of
the non-exact numbers `GW'(r; k, l)` over all `r`. As far as we know, the only exact value with
`k, l ≥ 3` known before was `H(3, 3) = 9`, which follows from the values of `GW(r; 3, 3)` (Mao,
Ozeki, Robertson and Wang; Y. Si, arXiv:2610.30711).

## The result (Quantavane, November 2026)

* `no_good_53`: every colouring of `[1, 53]`, with colours in any type, contains a rainbow 3-term AP
  or a monochromatic 4-term AP; `no_good_of_le`: the same for `[1, n]` with `n ≥ 53`.
* `exists_good_52`: some colouring of `[1, 52]` (with three colours) has neither.
* `H_four`: hence `H(3, 4) = 53`.
-/

namespace GwH34

/-- `c` is a *`(3, l)`-good colouring of `[1, n]`*: no `x, x + d, x + 2d` in `[1, n]` with `d ≥ 1`
has three distinct colours, and no `x, x + d, …, x + (l - 1)d` in `[1, n]` with `d ≥ 1` has all its
terms of one colour. The colours are elements of any type `α`, so the number of colours is not
bounded; the colouring is a function on all of `ℕ`, and its values outside `[1, n]` play no role. -/
def IsGood {α : Type} (l n : ℕ) (c : ℕ → α) : Prop :=
  (∀ x d : ℕ, 1 ≤ x → 1 ≤ d → x + 2 * d ≤ n →
    ¬ (c x ≠ c (x + d) ∧ c x ≠ c (x + 2 * d) ∧ c (x + d) ≠ c (x + 2 * d))) ∧
  (∀ x d : ℕ, 1 ≤ x → 1 ≤ d → x + (l - 1) * d ≤ n → ¬ ∀ j < l, c (x + j * d) = c x)

/-- The canonical Gallai–van der Waerden number `H(3, l)`: the least `N` such that no colouring of
`[1, N]` by natural numbers, with any number of colours, is `(3, l)`-good (Lean's `sInf`; the
infimum of the empty set of natural numbers is `0`). -/
noncomputable def H (l : ℕ) : ℕ := sInf {N | ∀ c : ℕ → ℕ, ¬ IsGood l N c}

/-- **No good colouring of `[1, 53]`.** Every colouring of `[1, 53]`, with colours in any type, has
a rainbow 3-term AP or a monochromatic 4-term AP. -/
theorem no_good_53 {α : Type} (c : ℕ → α) : ¬ IsGood 4 53 c := by
  sorry

/-- **No good colouring of `[1, n]` for `n ≥ 53`.** -/
theorem no_good_of_le {α : Type} (n : ℕ) (hn : 53 ≤ n) (c : ℕ → α) : ¬ IsGood 4 n c := by
  sorry

/-- **A good colouring of `[1, 52]`**: some colouring of `[1, 52]` by natural numbers has no rainbow
3-term AP and no monochromatic 4-term AP. -/
theorem exists_good_52 : ∃ c : ℕ → ℕ, IsGood 4 52 c := by
  sorry

/-- **`H(3, 4) = 53`.** -/
theorem H_four : H 4 = 53 := by
  sorry

end GwH34
