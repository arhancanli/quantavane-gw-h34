module

public import GwH34.Clauses
public import GwH34.Cert

@[expose] public section

/-!
# The upper bound: no colouring of `[1, 53]` is `(3, 4)`-good

`cert_ok` is the kernel check (`decide +kernel`, no `native_decide`) of the certificate
`GwH34.cert` against the any-colour CNF for `n = 53`: 702 derived clauses, 20,963 hints, the last
derived clause empty. With `checkH_sound` it shows that no colouring of `[1, 53]`, with values in
any type, has neither a rainbow 3-term nor a monochromatic 4-term progression.
-/

namespace GwH34

theorem cert_ok : checkH 53 cert = true := by decide +kernel

theorem no_good_53' {α : Type} (c : ℕ → α) : ¬ IsGood 4 53 c := checkH_sound (by decide) cert cert_ok c

end GwH34
