module

public import GwH34.Defs

@[expose] public section

/-!
# The lower bound: a `(3, 4)`-good colouring of `[1, 52]`

`goodB l n c` is a Boolean form of `IsGood l n c` for a colouring by natural numbers (loops over
`x, d ≤ n`), and `isGood_of_goodB` proves that it is sound for `l ≥ 2`. The colouring is the
3-colouring of `[1, 52]` of Quantavane's registered entry PALOMAR-2026-11-13-000005 (point 1 first):

`0221211122111212202212111221112122022121112211121222`

stored as a natural number in base 8 (point `x` gets the digit `x - 1`). It is checked by
`decide +kernel` (kernel evaluation of `goodB`; no `native_decide`).
-/

namespace GwH34

/-- Boolean form of `IsGood l n c` for a colouring by natural numbers. -/
def goodB (l n : ℕ) (c : ℕ → ℕ) : Bool :=
  ((List.range (n + 1)).all fun x => (List.range (n + 1)).all fun d =>
    !(decide (1 ≤ x) && decide (1 ≤ d) && decide (x + 2 * d ≤ n)) ||
    !(decide (c x ≠ c (x + d)) && decide (c x ≠ c (x + 2 * d)) && decide (c (x + d) ≠ c (x + 2 * d)))) &&
  ((List.range (n + 1)).all fun x => (List.range (n + 1)).all fun d =>
    !(decide (1 ≤ x) && decide (1 ≤ d) && decide (x + (l - 1) * d ≤ n)) ||
    (List.range l).any fun j => decide (c (x + j * d) ≠ c x))

theorem isGood_of_goodB {l n : ℕ} {c : ℕ → ℕ} (hl : 2 ≤ l) (h : goodB l n c = true) :
    IsGood l n c := by
  simp only [goodB, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, List.mem_range,
    Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_true_eq,
    decide_eq_false_iff_not] at h
  obtain ⟨hrb, hmono⟩ := h
  refine ⟨?_, ?_⟩
  · intro x d hx hd hxd ⟨h1, h2, h3⟩
    rcases hrb x (by omega) d (by omega) with (⟨h | h⟩ | h) | ((h | h) | h)
    · omega
    · omega
    · omega
    · exact h h1
    · exact h h2
    · exact h h3
  · intro x d hx hd hxd hall'
    have hdl : d ≤ (l - 1) * d := Nat.le_mul_of_pos_left d (by omega)
    rcases hmono x (by omega) d (by omega) with (⟨h | h⟩ | h) | ⟨j, hj, hne⟩
    · omega
    · omega
    · omega
    · exact hne (hall' j hj)

/-- The 3-colouring `0221211122111212202212111221112122022121112211121222` of `[1, 52]`: point
`x` gets the base-8 digit `x - 1`. -/
def col52 (x : ℕ) : ℕ := (0x49144948928a41228929125148245125224a290 >>> (3 * (x - 1))) % 8

theorem good52 : IsGood 4 52 col52 := isGood_of_goodB (by decide) (by decide +kernel)

end GwH34
