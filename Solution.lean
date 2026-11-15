module

public import GwH34

public section

/-!
# Proofs of the statements in `Challenge.lean`

Each theorem below has exactly the statement of its counterpart in `Challenge.lean` (Comparator
checks this, together with the definitions the statements use, which come from `GwH34.Defs`).

* `no_good_53`: `GwH34.Upper` (`cert_ok`: the kernel check of the LRAT certificate; `checkH_sound`:
  the checker's soundness and the truth of every descriptor clause for a good colouring);
* `no_good_of_le`: a good colouring of `[1, n]` restricts to one of `[1, 53]` (`isGood_mono`);
* `exists_good_52`: the explicit colouring of `GwH34.Lower`, checked by `decide +kernel`;
* `H_four`: both together.
-/

namespace GwH34

/-- A good colouring of `[1, n]` is good on `[1, m]` for `m ≤ n`. -/
theorem isGood_mono {α : Type} {l n m : ℕ} {c : ℕ → α} (h : IsGood l n c) (hm : m ≤ n) :
    IsGood l m c :=
  ⟨fun x d hx hd hxd => h.1 x d hx hd (by omega), fun x d hx hd hxd => h.2 x d hx hd (by omega)⟩

theorem no_good_53 {α : Type} (c : ℕ → α) : ¬ IsGood 4 53 c := no_good_53' c

theorem no_good_of_le {α : Type} (n : ℕ) (hn : 53 ≤ n) (c : ℕ → α) : ¬ IsGood 4 n c :=
  fun h => no_good_53 c (isGood_mono h hn)

theorem exists_good_52 : ∃ c : ℕ → ℕ, IsGood 4 52 c := ⟨col52, good52⟩

theorem H_four : H 4 = 53 := by
  have h53 : 53 ∈ {N | ∀ c : ℕ → ℕ, ¬ IsGood 4 N c} := fun c => no_good_53 c
  refine le_antisymm (Nat.sInf_le h53) (le_csInf ⟨53, h53⟩ fun N hN => ?_)
  by_contra hlt
  exact hN col52 (isGood_mono good52 (by omega))

end GwH34
