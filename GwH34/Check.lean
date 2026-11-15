module

@[expose] public section

/-!
# A RUP checker on bitmask clauses, written for evaluation by Lean's kernel

The upper bound `H(3, 4) ≤ 53` rests on an LRAT refutation of a CNF whose atoms say that two points
have the same colour. This file checks such a refutation inside the kernel (`decide +kernel`, no
`native_decide`). It is the checker of Quantavane's registered entry PALOMAR-2026-11-13-000005
(`GwExact.Check`), with wider fields: literals of 13 bits and counts of 16 bits.

* A clause is a pair of bitmasks `Cls` (bit `v` of `p`: the literal `v`; bit `v` of `n`: the
  literal `¬ v`), so unit propagation is a handful of operations on natural numbers, which the
  kernel performs with GMP (`Nat.land`, `Nat.lor`, `Nat.xor`, shifts).
* A hint names either an original clause, through a *source* function (here the clause is
  recomputed from a short descriptor, `GwH34.Clauses`), or an earlier derived clause, kept in a
  binary trie (`Trie`).
* `rup` performs reverse unit propagation; `run` checks the derived clauses in order and succeeds
  once the empty clause is derived.

Soundness (`run_sound`) is proved for every input: if every clause the source returns is true
under an assignment `σ`, then `run` cannot succeed. The certificate (`GwH34.Cert`) is untrusted
data. All functions use structural recursion and call the `Nat` primitives directly, so that the
kernel evaluates them without unfolding instances.
-/

namespace GwH34

/-- A clause as two bitmasks: bit `v` of `p` is the literal `v`, bit `v` of `n` the literal `¬ v`. -/
structure Cls where
  p : Nat
  n : Nat

/-- The assignment `σ` satisfies the clause `c`: some literal of `c` is true under `σ`. -/
def Cls.Holds (σ : Nat → Bool) (c : Cls) : Prop :=
  ∃ v, (c.p.testBit v = true ∧ σ v = true) ∨ (c.n.testBit v = true ∧ σ v = false)

/-- A binary trie of clauses keyed by natural numbers (bijective base 2, least significant digit
first): the root holds key `0`, the left subtree the keys `2k + 1`, the right one `2k + 2`. -/
inductive Trie where
  | leaf : Trie
  | node : Trie → Option Cls → Trie → Trie

/-- Look up a key. -/
def Trie.find : Trie → Nat → Option Cls
  | .leaf, _ => none
  | .node l v r, k =>
    cond (Nat.beq k 0) v
      (cond (Nat.beq (Nat.land k 1) 1) (Trie.find l (Nat.shiftRight k 1))
        (Trie.find r (Nat.sub (Nat.shiftRight k 1) 1)))

/-- The parts of a trie node (a leaf has empty parts). -/
def Trie.left : Trie → Trie
  | .leaf => .leaf
  | .node l _ _ => l

def Trie.val : Trie → Option Cls
  | .leaf => none
  | .node _ v _ => v

def Trie.right : Trie → Trie
  | .leaf => .leaf
  | .node _ _ r => r

/-- Insert a clause at a key (`fuel` bounds the depth; with too little fuel nothing is inserted). -/
def Trie.ins : Nat → Trie → Nat → Cls → Trie
  | 0, t, _, _ => t
  | f + 1, t, k, c =>
    cond (Nat.beq k 0) (.node t.left (some c) t.right)
      (cond (Nat.beq (Nat.land k 1) 1) (.node (Trie.ins f t.left (Nat.shiftRight k 1) c) t.val t.right)
        (.node t.left t.val (Trie.ins f t.right (Nat.sub (Nat.shiftRight k 1) 1) c)))

/-- Read `cnt` literals of 13 bits each (`2 * atom + 1` for the literal `atom`, `2 * atom` for
`¬ atom`) from `code` into the masks `p`, `n`; return the clause and the rest of `code`. -/
def readLits : Nat → Nat → Nat → Nat → Cls × Nat
  | 0, code, p, n => (⟨p, n⟩, code)
  | c + 1, code, p, n =>
    cond (Nat.beq (Nat.land code 1) 1)
      (readLits c (Nat.shiftRight code 13)
        (Nat.lor p (Nat.shiftLeft 1 (Nat.shiftRight (Nat.land code 8191) 1))) n)
      (readLits c (Nat.shiftRight code 13) p
        (Nat.lor n (Nat.shiftLeft 1 (Nat.shiftRight (Nat.land code 8191) 1))))

/-- Reverse unit propagation over `cnt` hints of `w` bits each (`wm = 2 ^ w - 1`) read from
`code`. The atoms in `t` are true and those in `f` false. A hint clause with no unfalsified
literal is a conflict (`true`); one with exactly one unfalsified literal makes it true; anything
else fails (`false`). -/
def rup (src : Nat → Option Cls) (w wm : Nat) : Nat → Nat → Nat → Nat → Bool
  | 0, _, _, _ => false
  | c + 1, code, t, f =>
    match src (Nat.land code wm) with
    | none => false
    | some cl =>
      let rp := Nat.xor cl.p (Nat.land cl.p f)
      let rn := Nat.xor cl.n (Nat.land cl.n t)
      cond (Nat.beq rp 0)
        (cond (Nat.beq rn 0) true
          (cond (Nat.beq (Nat.land rn (Nat.sub rn 1)) 0)
            (rup src w wm c (Nat.shiftRight code w) t (Nat.lor f rn)) false))
        (cond (Nat.beq rn 0 && Nat.beq (Nat.land rp (Nat.sub rp 1)) 0)
          (rup src w wm c (Nat.shiftRight code w) (Nat.lor t rp) f) false)

/-- Check the derived clauses in order. Step `s`: 16 bits literal count, the literals (`readLits`),
16 bits hint count, the hints. The clause is checked by `rup` from its negation, then stored at
index `i`. `true` once the empty clause has been derived. `src db h` is the clause of hint `h`. -/
def run (src : Trie → Nat → Option Cls) (w wm : Nat) : Trie → Nat → List Nat → Bool
  | _, _, [] => false
  | db, i, s :: ss =>
    match readLits (Nat.land s 65535) (Nat.shiftRight s 16) 0 0 with
    | (cl, rest) =>
      cond (rup (src db) w wm (Nat.land rest 65535) (Nat.shiftRight rest 16) cl.n cl.p)
        (cond (Nat.beq cl.p 0 && Nat.beq cl.n 0) true
          (run src w wm (Trie.ins 32 db i cl) (Nat.add i 1) ss))
        false

/-! ## Soundness -/

/-- Every clause stored in the trie is true under `σ`. -/
def Good (σ : Nat → Bool) (db : Trie) : Prop :=
  ∀ k c, db.find k = some c → c.Holds σ

theorem good_leaf (σ : Nat → Bool) : Good σ .leaf := by
  intro k c h
  simp [Trie.find] at h

theorem land_one (k : Nat) : Nat.land k 1 = k % 2 := Nat.and_one_is_mod k

theorem shiftRight_one (k : Nat) : Nat.shiftRight k 1 = k / 2 := by
  show k >>> 1 = k / 2
  simp [Nat.shiftRight_eq_div_pow]

theorem find_node (l r : Trie) (v : Option Cls) (k : Nat) :
    (Trie.node l v r).find k =
      if k = 0 then v else if k % 2 = 1 then l.find (k / 2) else r.find (k / 2 - 1) := by
  simp only [Trie.find, land_one, shiftRight_one, Bool.cond_eq_ite, Nat.beq_eq, Nat.sub_eq]

/-- `find` in terms of the parts of a trie (also for a leaf). -/
theorem find_parts (t : Trie) (k : Nat) :
    t.find k = if k = 0 then t.val else if k % 2 = 1 then t.left.find (k / 2) else t.right.find (k / 2 - 1) := by
  cases t with
  | leaf => simp [Trie.find, Trie.val, Trie.left, Trie.right]
  | node l v r => rw [find_node]; rfl

theorem ins_succ (f : Nat) (t : Trie) (k : Nat) (c : Cls) :
    Trie.ins (f + 1) t k c =
      if k = 0 then .node t.left (some c) t.right
      else if k % 2 = 1 then .node (Trie.ins f t.left (k / 2) c) t.val t.right
      else .node t.left t.val (Trie.ins f t.right (k / 2 - 1) c) := by
  simp only [Trie.ins, land_one, shiftRight_one, Bool.cond_eq_ite, Nat.beq_eq, Nat.sub_eq]

/-- A value found after an insertion is the inserted clause or was found before. -/
theorem find_ins : ∀ (f : Nat) (t : Trie) (k : Nat) (c : Cls) (k' : Nat) (c' : Cls),
    (Trie.ins f t k c).find k' = some c' → c' = c ∨ t.find k' = some c' := by
  intro f
  induction f with
  | zero => intro t k c k' c' h; exact Or.inr h
  | succ f ih =>
    intro t k c k' c' h
    rw [find_parts t k']
    rw [ins_succ] at h
    split at h
    · rw [find_node] at h
      split at h
      · exact Or.inl (Option.some.inj h).symm
      · right; simp_all
    · split at h
      · rw [find_node] at h
        split at h
        · right; simp_all
        · split at h
          · rcases ih _ _ _ _ _ h with h5 | h5
            · exact Or.inl h5
            · right; simp_all
          · right; simp_all
      · rw [find_node] at h
        split at h
        · right; simp_all
        · split at h
          · right; simp_all
          · rcases ih _ _ _ _ _ h with h5 | h5
            · exact Or.inl h5
            · right; simp_all

theorem good_ins {σ : Nat → Bool} {db : Trie} (hdb : Good σ db) (f k : Nat) {c : Cls}
    (hc : c.Holds σ) : Good σ (Trie.ins f db k c) := by
  intro k' c' h
  rcases find_ins f db k c k' c' h with h1 | h1
  · exact h1 ▸ hc
  · exact hdb k' c' h1

/-- `x &&& (x - 1) = 0` leaves at most one bit of `x` set. -/
theorem eq_of_land_pred (x : Nat) : Nat.land x (x - 1) = 0 →
    ∀ u v, x.testBit u = true → x.testBit v = true → u = v := by
  induction x using Nat.strongRecOn with
  | ind x ih =>
    intro hx u v hu hv
    have key : ∀ i, (x &&& (x - 1)).testBit i = false := by
      intro i; have : x &&& (x - 1) = 0 := hx; rw [this]; simp
    have hsucc : ∀ y i, y.testBit (i + 1) = (y / 2).testBit i := fun y i => Nat.testBit_succ y i
    rcases Nat.mod_two_eq_zero_or_one x with hx2 | hx2
    · -- x even
      have hy : x / 2 < x := by
        have : x ≠ 0 := by rintro rfl; simp at hu
        omega
      have hy' : Nat.land (x / 2) (x / 2 - 1) = 0 := by
        apply Nat.eq_of_testBit_eq
        intro i
        have := key (i + 1)
        rw [Nat.testBit_and, hsucc, hsucc, show (x - 1) / 2 = x / 2 - 1 by omega] at this
        show ((x / 2) &&& (x / 2 - 1)).testBit i = Nat.testBit 0 i
        rw [Nat.testBit_and, this]; simp
      have h0 : x.testBit 0 = false := by simp [Nat.testBit_zero, hx2]
      cases u with
      | zero => rw [h0] at hu; exact absurd hu (by simp)
      | succ u =>
        cases v with
        | zero => rw [h0] at hv; exact absurd hv (by simp)
        | succ v =>
          rw [hsucc] at hu hv
          have := ih (x / 2) hy hy' u v hu hv
          omega
    · -- x odd
      have hhalf : x / 2 = 0 := by
        apply Nat.eq_of_testBit_eq
        intro i
        have := key (i + 1)
        rw [Nat.testBit_and, hsucc, hsucc, show (x - 1) / 2 = x / 2 by omega, Bool.and_self] at this
        simp [this]
      have hsmall : ∀ w, x.testBit w = true → w = 0 := by
        intro w hw
        cases w with
        | zero => rfl
        | succ w => rw [hsucc, hhalf] at hw; simp at hw
      rw [hsmall u hu, hsmall v hv]

theorem testBit_rem (a b v : Nat) :
    (Nat.xor a (Nat.land a b)).testBit v = (a.testBit v && !b.testBit v) := by
  show (a ^^^ (a &&& b)).testBit v = _
  rw [Nat.testBit_xor, Nat.testBit_and]
  cases a.testBit v <;> cases b.testBit v <;> rfl

theorem testBit_lor (a b v : Nat) : (Nat.lor a b).testBit v = (a.testBit v || b.testBit v) :=
  Nat.testBit_or a b v

theorem beq_false {a b : Nat} (h : ¬ a = b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hb) h

theorem beq_true {a b : Nat} (h : a = b) : Nat.beq a b = true := by
  subst h; exact Nat.beq_refl a

/-- Soundness of reverse unit propagation: if every clause from `src` is true under `σ` and `σ`
agrees with the partial assignment `(t, f)`, the propagation cannot reach a conflict. -/
theorem rup_sound {σ : Nat → Bool} {src : Nat → Option Cls} {w wm : Nat}
    (hsrc : ∀ h c, src h = some c → c.Holds σ) :
    ∀ cnt code t f, rup src w wm cnt code t f = true →
      (∀ v, t.testBit v = true → σ v = true) → (∀ v, f.testBit v = true → σ v = false) → False := by
  intro cnt
  induction cnt with
  | zero => intro code t f h; simp [rup] at h
  | succ cnt ih =>
    intro code t f h ht hf
    simp only [rup] at h
    split at h
    · simp at h
    · rename_i cl hcl
      obtain ⟨v, hv⟩ := hsrc _ _ hcl
      have hrp : ∀ u, (Nat.xor cl.p (Nat.land cl.p f)).testBit u = (cl.p.testBit u && !f.testBit u) :=
        fun u => testBit_rem _ _ u
      have hrn : ∀ u, (Nat.xor cl.n (Nat.land cl.n t)).testBit u = (cl.n.testBit u && !t.testBit u) :=
        fun u => testBit_rem _ _ u
      -- the true literal of the hint clause is not falsified
      have hlive : (Nat.xor cl.p (Nat.land cl.p f)).testBit v = true ∨
          (Nat.xor cl.n (Nat.land cl.n t)).testBit v = true := by
        rcases hv with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · left; rw [hrp, h1]
          cases hfv : f.testBit v
          · rfl
          · have := hf v hfv; rw [h2] at this; exact absurd this (by simp)
        · right; rw [hrn, h1]
          cases htv : t.testBit v
          · rfl
          · have := ht v htv; rw [h2] at this; exact absurd this (by simp)
      generalize hRP : Nat.xor cl.p (Nat.land cl.p f) = rp at h hrp hlive
      generalize hRN : Nat.xor cl.n (Nat.land cl.n t) = rn at h hrn hlive
      by_cases hp0 : rp = 0
      · subst hp0
        have hlive' : rn.testBit v = true := by simpa using hlive
        by_cases hn0 : rn = 0
        · subst hn0; simp at hlive'
        · have hb : Nat.beq rn 0 = false := beq_false hn0
          simp only [Nat.beq_refl, Bool.cond_true, hb, Bool.cond_false] at h
          by_cases hpow : Nat.land rn (rn - 1) = 0
          · have hb2 : Nat.beq (Nat.land rn (Nat.sub rn 1)) 0 = true := beq_true hpow
            rw [hb2, Bool.cond_true] at h
            refine ih _ _ _ h ht ?_
            intro u hu
            have hu' : (f ||| rn).testBit u = true := hu
            rw [Nat.testBit_or] at hu'
            rcases Bool.or_eq_true_iff.mp hu' with hu1 | hu1
            · exact hf u hu1
            · have := eq_of_land_pred rn hpow u v hu1 hlive'
              subst this
              have := (hrn u).symm.trans hu1
              rcases hv with ⟨h1, h2⟩ | ⟨h1, h2⟩
              · -- v is a positive literal of cl; rp = 0 forces f v
                exfalso
                have hz : (0 : Nat).testBit u = (cl.p.testBit u && !f.testBit u) := hrp u
                rw [h1] at hz
                cases hfu : f.testBit u
                · rw [hfu] at hz; simp at hz
                · have := hf u hfu; rw [h2] at this; exact absurd this (by simp)
              · exact h2
          · have hb2 : Nat.beq (Nat.land rn (Nat.sub rn 1)) 0 = false := beq_false hpow
            rw [hb2, Bool.cond_false] at h
            simp at h
      · have hb : Nat.beq rp 0 = false := beq_false hp0
        simp only [hb, Bool.cond_false] at h
        by_cases hn0 : rn = 0
        · subst hn0
          have hlive' : rp.testBit v = true := by simpa using hlive
          by_cases hpow : Nat.land rp (rp - 1) = 0
          · have hb2 : (Nat.beq 0 0 && Nat.beq (Nat.land rp (Nat.sub rp 1)) 0) = true := by
              rw [Nat.beq_refl, show Nat.beq (Nat.land rp (Nat.sub rp 1)) 0 = true from beq_true hpow]; rfl
            rw [hb2, Bool.cond_true] at h
            refine ih _ _ _ h ?_ hf
            intro u hu
            have hu' : (t ||| rp).testBit u = true := hu
            rw [Nat.testBit_or] at hu'
            rcases Bool.or_eq_true_iff.mp hu' with hu1 | hu1
            · exact ht u hu1
            · have := eq_of_land_pred rp hpow u v hu1 hlive'
              subst this
              rcases hv with ⟨h1, h2⟩ | ⟨h1, h2⟩
              · exact h2
              · exfalso
                have hz : (0 : Nat).testBit u = (cl.n.testBit u && !t.testBit u) := hrn u
                rw [h1] at hz
                cases htu : t.testBit u
                · rw [htu] at hz; simp at hz
                · have := ht u htu; rw [h2] at this; exact absurd this (by simp)
          · have hb2 : (Nat.beq 0 0 && Nat.beq (Nat.land rp (Nat.sub rp 1)) 0) = false := by
              rw [Nat.beq_refl, show Nat.beq (Nat.land rp (Nat.sub rp 1)) 0 = false from beq_false hpow]; rfl
            rw [hb2, Bool.cond_false] at h
            simp at h
        · have hb2 : Nat.beq rn 0 = false := beq_false hn0
          rw [hb2, Bool.false_and, Bool.cond_false] at h
          simp at h

/-- Soundness of the main loop: if every clause the source returns (for a trie of true clauses)
is true under `σ`, no run succeeds. -/
theorem run_sound {σ : Nat → Bool} {src : Trie → Nat → Option Cls} {w wm : Nat}
    (hsrc : ∀ db, Good σ db → ∀ h c, src db h = some c → c.Holds σ) :
    ∀ (steps : List Nat) (db : Trie) (i : Nat), Good σ db → run src w wm db i steps = true → False := by
  intro steps
  induction steps with
  | nil => intro db i _ h; simp [run] at h
  | cons s ss ih =>
    intro db i hdb h
    simp only [run] at h
    generalize hr : readLits (Nat.land s 65535) (Nat.shiftRight s 16) 0 0 = res at h
    obtain ⟨cl, rest⟩ := res
    simp only at h
    cases hc : rup (src db) w wm (Nat.land rest 65535) (Nat.shiftRight rest 16) cl.n cl.p with
    | false => rw [hc, Bool.cond_false] at h; exact absurd h (by simp)
    | true =>
      rw [hc, Bool.cond_true] at h
      -- the derived clause is true under σ
      have hholds : cl.Holds σ := by
        refine Classical.byContradiction fun hno => ?_
        apply rup_sound (hsrc db hdb) _ _ _ _ hc
        · intro v hv
          cases hσ : σ v
          · exact absurd ⟨v, Or.inr ⟨hv, hσ⟩⟩ hno
          · rfl
        · intro v hv
          cases hσ : σ v
          · rfl
          · exact absurd ⟨v, Or.inl ⟨hv, hσ⟩⟩ hno
      by_cases he : Nat.beq cl.p 0 && Nat.beq cl.n 0
      · obtain ⟨v, hv⟩ := hholds
        simp only [Bool.and_eq_true, Nat.beq_eq] at he
        rw [he.1, he.2] at hv
        simp at hv
      · rw [Bool.not_eq_true] at he
        rw [he, Bool.cond_false] at h
        exact ih _ _ (good_ins hdb 32 i hholds) h

end GwH34
