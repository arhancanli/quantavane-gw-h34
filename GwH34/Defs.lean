module

public import Mathlib.Order.Lattice.Nat

@[expose] public section

/-!
# Definitions used by the proof

These are the two definitions of `Challenge.lean`, with the same imports and the same text, so that
the proof is about exactly the notions the statement uses (Comparator checks that the declarations
agree). See `Challenge.lean` for the mathematical account.
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

end GwH34
