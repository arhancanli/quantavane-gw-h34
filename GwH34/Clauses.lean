module

public import GwH34.Check
public import GwH34.Defs

@[expose] public section

/-!
# The clauses of the any-colour CNF, recomputed from descriptors

The CNF behind `H(3, 4) ≤ 53` (Quantavane's `gw_eq.py 53 4 0`) describes a colouring of the
positions `0, …, n - 1` (the points `1, …, n`) with any number of colours through the atoms
`atom i j = 64 i + j` (`i < j`), which say that positions `i` and `j` have the same colour. Its
clauses: transitivity for every triple of positions; for every 3-term progression, two of its terms
have the same colour (no rainbow 3-term progression); for every `l`-term progression, two
consecutive terms have different colours (no monochromatic `l`-term progression; here `l = 4`).

Instead of building the CNF (71,396 clauses), the checker recomputes each clause a hint names from
a short descriptor (`descCls`), and `descCls_holds` shows that every such clause is true for the
assignment `asgE c` of a good colouring `c` of `[1, n]`, `n ≤ 64`.

Descriptor layout (least significant bits first): kind (2 bits), then fields `f1, …, f4` of 6 bits.
* kind 0: transitivity of the triple `f1 < f2 < f3 < n`: clause `f4` among
  `¬e(f1,f2) ∨ ¬e(f2,f3) ∨ e(f1,f3)`, `¬e(f1,f2) ∨ ¬e(f1,f3) ∨ e(f2,f3)`,
  `¬e(f1,f3) ∨ ¬e(f2,f3) ∨ e(f1,f2)`;
* kind 1: `e(a, a+d) ∨ e(a+d, a+2d) ∨ e(a, a+2d)` for `a = f1`, `d = f2 ≥ 1`, `a + 2d < n`;
* kind 2: `¬e(a, a+d) ∨ ¬e(a+d, a+2d) ∨ ¬e(a+2d, a+3d)` for `a = f1`, `d = f2 ≥ 1`, `a + 3d < n`.
-/

namespace GwH34

/-- The bit of atom `v`. -/
def bit (v : Nat) : Nat := Nat.shiftLeft 1 v

/-- The atom "positions `i` and `j` have the same colour" (for `i < j < 64`). -/
def atm (i j : Nat) : Nat := Nat.add (Nat.mul i 64) j

/-- The clause of a descriptor, or `none` for an invalid descriptor. -/
def descCls (n code : Nat) : Option Cls :=
  let kind := Nat.land code 3
  let f1 := Nat.land (Nat.shiftRight code 2) 63
  let f2 := Nat.land (Nat.shiftRight code 8) 63
  let f3 := Nat.land (Nat.shiftRight code 14) 63
  let f4 := Nat.land (Nat.shiftRight code 20) 63
  cond (Nat.beq kind 0)
    (cond (Nat.blt f1 f2 && Nat.blt f2 f3 && Nat.blt f3 n)
      (cond (Nat.beq f4 0)
        (some ⟨bit (atm f1 f3), Nat.lor (bit (atm f1 f2)) (bit (atm f2 f3))⟩)
      (cond (Nat.beq f4 1)
        (some ⟨bit (atm f2 f3), Nat.lor (bit (atm f1 f2)) (bit (atm f1 f3))⟩)
      (cond (Nat.beq f4 2)
        (some ⟨bit (atm f1 f2), Nat.lor (bit (atm f1 f3)) (bit (atm f2 f3))⟩) none))) none)
  (cond (Nat.beq kind 1)
    (cond (Nat.ble 1 f2 && Nat.blt (Nat.add f1 (Nat.mul 2 f2)) n)
      (some ⟨Nat.lor (Nat.lor (bit (atm f1 (Nat.add f1 f2))) (bit (atm (Nat.add f1 f2) (Nat.add f1 (Nat.mul 2 f2)))))
        (bit (atm f1 (Nat.add f1 (Nat.mul 2 f2)))), 0⟩) none)
  (cond (Nat.beq kind 2)
    (cond (Nat.ble 1 f2 && Nat.blt (Nat.add f1 (Nat.mul 3 f2)) n)
      (some ⟨0, Nat.lor (Nat.lor (bit (atm f1 (Nat.add f1 f2))) (bit (atm (Nat.add f1 f2) (Nat.add f1 (Nat.mul 2 f2)))))
        (bit (atm (Nat.add f1 (Nat.mul 2 f2)) (Nat.add f1 (Nat.mul 3 f2))))⟩) none)
  none))

/-- The clause source of the certificate: odd hints name derived clauses (by index), even hints
name original clauses (by descriptor). -/
def hSrc (n : Nat) (db : Trie) (h : Nat) : Option Cls :=
  cond (Nat.beq (Nat.land h 1) 1) (db.find (Nat.shiftRight h 1)) (descCls n (Nat.shiftRight h 1))

/-- The checker for the any-colour CNF with hints of 28 bits. -/
def checkH (n : Nat) (steps : List Nat) : Bool :=
  run (hSrc n) 28 268435455 .leaf 0 steps

/-! ## Soundness -/

open Classical in
/-- The assignment of a colouring: atom `v` is true iff positions `v / 64` and `v % 64` (the points
`v / 64 + 1` and `v % 64 + 1`) have the same colour. -/
noncomputable def asgE {α : Type} (c : ℕ → α) (v : Nat) : Bool := decide (c (v / 64 + 1) = c (v % 64 + 1))

open Classical in
theorem asgE_atm {α : Type} {c : ℕ → α} {i j : Nat} (hj : j < 64) :
    asgE c (atm i j) = true ↔ c (i + 1) = c (j + 1) := by
  have h1 : (i * 64 + j) / 64 = i := by omega
  have h2 : (i * 64 + j) % 64 = j := by omega
  show decide (c ((i * 64 + j) / 64 + 1) = c ((i * 64 + j) % 64 + 1)) = true ↔ _
  rw [h1, h2, decide_eq_true_iff]

theorem testBit_bit (v u : Nat) : (bit v).testBit u = decide (v = u) := by
  show (1 <<< v).testBit u = _
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow]

theorem testBit_lor' (a b u : Nat) : (Nat.lor a b).testBit u = (a.testBit u || b.testBit u) :=
  Nat.testBit_or a b u

/-- A positive literal `e(i, j)` that is true makes the clause true. -/
theorem holds_pos {α : Type} {c : ℕ → α} {cl : Cls} {i j : Nat} (hj : j < 64)
    (hbit : cl.p.testBit (atm i j) = true) (heq : c (i + 1) = c (j + 1)) : cl.Holds (asgE c) :=
  ⟨atm i j, Or.inl ⟨hbit, (asgE_atm hj).mpr heq⟩⟩

/-- A negative literal `¬ e(i, j)` that is true makes the clause true. -/
theorem holds_neg {α : Type} {c : ℕ → α} {cl : Cls} {i j : Nat} (hj : j < 64)
    (hbit : cl.n.testBit (atm i j) = true) (hne : c (i + 1) ≠ c (j + 1)) : cl.Holds (asgE c) := by
  refine ⟨atm i j, Or.inr ⟨hbit, ?_⟩⟩
  cases h : asgE c (atm i j)
  · rfl
  · exact absurd ((asgE_atm hj).mp h) hne

theorem bit_self (v : Nat) : (bit v).testBit v = true := by rw [testBit_bit]; simp

theorem lor_left {a b u : Nat} (h : a.testBit u = true) : (Nat.lor a b).testBit u = true := by
  rw [testBit_lor', h]; rfl

theorem lor_right {a b u : Nat} (h : b.testBit u = true) : (Nat.lor a b).testBit u = true := by
  rw [testBit_lor', h, Bool.or_true]

/-- Every clause computed from a descriptor is true for the assignment of a `(3, 4)`-good colouring
of `[1, n]`, `n ≤ 64`. -/
theorem descCls_holds {α : Type} {n : Nat} (hn : n ≤ 64) {c : ℕ → α} (hc : IsGood 4 n c)
    (code : Nat) {cl : Cls} (h : descCls n code = some cl) : cl.Holds (asgE c) := by
  simp only [descCls, Bool.cond_eq_ite, Nat.beq_eq, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq,
    Nat.add_eq, Nat.mul_eq] at h
  generalize Nat.land code 3 = kind at h
  generalize Nat.land (Nat.shiftRight code 2) 63 = f1 at h
  generalize Nat.land (Nat.shiftRight code 8) 63 = f2 at h
  generalize Nat.land (Nat.shiftRight code 14) 63 = f3 at h
  generalize Nat.land (Nat.shiftRight code 20) 63 = f4 at h
  obtain ⟨hrb, hmono⟩ := hc
  split at h
  · -- kind 0: transitivity
    split at h
    · rename_i hv
      obtain ⟨⟨h12, h23⟩, h3n⟩ := hv
      have b2 : f2 < 64 := by omega
      have b3 : f3 < 64 := by omega
      split at h
      · cases h
        by_cases e1 : c (f1 + 1) = c (f2 + 1)
        · by_cases e2 : c (f2 + 1) = c (f3 + 1)
          · exact holds_pos b3 (bit_self _) (e1.trans e2)
          · exact holds_neg b3 (lor_right (bit_self _)) e2
        · exact holds_neg b2 (lor_left (bit_self _)) e1
      split at h
      · cases h
        by_cases e1 : c (f1 + 1) = c (f2 + 1)
        · by_cases e2 : c (f1 + 1) = c (f3 + 1)
          · exact holds_pos b3 (bit_self _) (e1.symm.trans e2)
          · exact holds_neg b3 (lor_right (bit_self _)) e2
        · exact holds_neg b2 (lor_left (bit_self _)) e1
      split at h
      · cases h
        by_cases e1 : c (f1 + 1) = c (f3 + 1)
        · by_cases e2 : c (f2 + 1) = c (f3 + 1)
          · exact holds_pos b2 (bit_self _) (e1.trans e2.symm)
          · exact holds_neg b3 (lor_right (bit_self _)) e2
        · exact holds_neg b3 (lor_left (bit_self _)) e1
      · cases h
    · cases h
  split at h
  · -- kind 1: no rainbow 3-term progression
    split at h
    · cases h
      rename_i hv
      obtain ⟨hd, han⟩ := hv
      have hnot := hrb (f1 + 1) f2 (by omega) hd (by omega)
      have hb1 : f1 + f2 < 64 := by omega
      have hb2 : f1 + 2 * f2 < 64 := by omega
      by_cases e1 : c (f1 + 1) = c (f1 + f2 + 1)
      · exact holds_pos hb1 (lor_left (lor_left (bit_self _))) e1
      by_cases e2 : c (f1 + f2 + 1) = c (f1 + 2 * f2 + 1)
      · exact holds_pos hb2 (lor_left (lor_right (bit_self _))) e2
      by_cases e3 : c (f1 + 1) = c (f1 + 2 * f2 + 1)
      · exact holds_pos hb2 (lor_right (bit_self _)) e3
      exfalso
      apply hnot
      refine ⟨?_, ?_, ?_⟩
      · rwa [show f1 + 1 + f2 = f1 + f2 + 1 by omega]
      · rwa [show f1 + 1 + 2 * f2 = f1 + 2 * f2 + 1 by omega]
      · rwa [show f1 + 1 + f2 = f1 + f2 + 1 by omega, show f1 + 1 + 2 * f2 = f1 + 2 * f2 + 1 by omega]
    · cases h
  split at h
  · -- kind 2: no monochromatic 4-term progression
    split at h
    · cases h
      rename_i hv
      obtain ⟨hd, han⟩ := hv
      have hnot := hmono (f1 + 1) f2 (by omega) hd (by omega)
      have hb1 : f1 + f2 < 64 := by omega
      have hb2 : f1 + 2 * f2 < 64 := by omega
      have hb3 : f1 + 3 * f2 < 64 := by omega
      by_cases e1 : c (f1 + 1) = c (f1 + f2 + 1)
      · by_cases e2 : c (f1 + f2 + 1) = c (f1 + 2 * f2 + 1)
        · by_cases e3 : c (f1 + 2 * f2 + 1) = c (f1 + 3 * f2 + 1)
          · exfalso
            apply hnot
            intro j hj
            rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
            · simp
            · rw [show f1 + 1 + 1 * f2 = f1 + f2 + 1 by omega]; exact e1.symm
            · rw [show f1 + 1 + 2 * f2 = f1 + 2 * f2 + 1 by omega]; exact (e1.trans e2).symm
            · rw [show f1 + 1 + 3 * f2 = f1 + 3 * f2 + 1 by omega]; exact (e1.trans (e2.trans e3)).symm
          · exact holds_neg hb3 (lor_right (bit_self _)) e3
        · exact holds_neg hb2 (lor_left (lor_right (bit_self _))) e2
      · exact holds_neg hb1 (lor_left (lor_left (bit_self _))) e1
    · cases h
  · cases h

/-- **Soundness for the any-colour CNF.** If the checker accepts a certificate for `n ≤ 64`, no
colouring of `[1, n]` with values in any type is `(3, 4)`-good. -/
theorem checkH_sound {n : Nat} (hn : n ≤ 64) (steps : List Nat) (h : checkH n steps = true)
    {α : Type} (c : ℕ → α) : ¬ IsGood 4 n c := by
  intro hc
  refine run_sound (σ := asgE c) ?_ steps .leaf 0 (good_leaf _) h
  intro db hdb hint cl hcl
  unfold hSrc at hcl
  cases hb : Nat.beq (Nat.land hint 1) 1
  · rw [hb, Bool.cond_false] at hcl
    exact descCls_holds hn hc _ hcl
  · rw [hb, Bool.cond_true] at hcl
    exact hdb _ _ hcl

end GwH34
