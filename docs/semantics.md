# Source-to-Lean semantic contract (draft v1)

This contract describes the **intended** meaning of conservative verification
and the checks implemented today. It is not a translation correctness theorem.
The machine-readable inventory is [support-table.json](support-table.json).
`docs/verification.md` defines the current CLI and proof-status behavior.

## Claim and observations

For a pure, first-order source function `p`, translated definition `pᴸ`, and
related arguments `x ~ xᴸ`, the partial-correctness target is:

```text
AcceptedTranslation(p) ∧ x ~ xᴸ ∧ HaskellEval(p, x) ⇓ v
  ⇒ ∃ vᴸ, LeanEval(pᴸ, xᴸ) ⇓ vᴸ ∧ v ~ vᴸ.
```

`⇓` means evaluation terminates with an observable value. Divergence and
exceptions are outside the premise. The implication does **not** authorize an
arbitrary Lean value on a Haskell input that diverges or throws when a theorem
quantifies over all inputs. Such functions need a domain predicate carried into
the theorem, or a separate totality/definedness argument. Today conservative
mode refuses named partial operations and potentially infinite generators rather
than generating these obligations. General laziness and bottom are not modeled.
Finite lists are related elementwise when both sides produce a finite list;
this does not identify a Haskell infinite list with a Lean `List`.

The intended value relation is structural: `Integer` ↔ Lean `Int` by equal
mathematical value; `Bool` ↔ `Bool` by constructor; machine `Int` ↔ Lean `Int64`
by equal signed 64-bit value; finite lists and finite algebraic data by matching
constructors and related fields; tuples by related components. For `Char`, only
code points representable by Lean `Char` are related, so a Haskell lone
surrogate has no image. `String` is a finite `[Char]` and is modeled as Lean
`List Char` on that representable domain. `Word`, floating-point types, and
other fixed-width numeric types have no conservative relation yet.

The source observation must use the pinned GHC 9.2.7 build, package plan, and
target flags used for extraction. Conservative `Int` requires a measured 64-bit
target; it wraps on arithmetic and conversion from `Integer`. The currently
implemented checker uses `ghc-9.2.7 --info` for this gate. A theorem about a
different target is not covered by that run.

## Translation and proof boundaries

`AcceptedTranslation` currently means only that the conservative safety pass
found no **known** approximation and the translator finished without warnings.
The pass checks filtered Core before type and dictionary erasure, including
datatype fields, method types, and instance heads. It does not validate all
dictionary selection, coercion erasure, name resolution, imported definitions,
newtype representation, or annotation name binding. These are translator
assumptions, not Lean proof axioms. Passing the gate cannot establish the
implication above. Differential comparisons against GHC provide sampled
evidence for individual mappings, not a proof for all inputs or programs.

Imported Haskell definitions and instance dictionaries are in the source
semantics and must be translated with the same identities and behavior as at
the call site. Until typed identity and dictionary preservation exist, this is
an unproved assumption even for a successful conservative run. An imported
module outside the translated graph is especially not covered. Newtypes can
erase at runtime, but their type and instance identities still matter; their
current support is conditional and cannot be generalized from a single fixture.

A Lean `proved` status certifies the elaborated theorem **of the generated Lean
model**, conditional on Lean's trusted environment and the audited standard
axioms `propext`, `Classical.choice`, and `Quot.sound`. It does not certify that
the generated theorem states the intended Haskell property. `smt_valid` uses
`Blaster.Tactic.blasterProven`, an extra axiom without proof reconstruction; it
is accepted only when the caller explicitly passes `--trust-smt`. `sorryAx`,
other user axioms, and admitted termination are rejected. A Blaster refutation
is of the Lean model; replay against GHC is needed before calling it a Haskell
counterexample. The result presently records `claim: lean-model` and
`translationCertified: false` under both semantic modes.

## Change rule

An entry may move from `refused` or `conditional` to `guarded` only with a GHC
observation, an adversarial boundary case, a deliberately false property, a
Lean axiom report, and a test of the remaining refusal domain. Record the
specific source-to-Lean assumption separately from proof axioms. A mechanical
correspondence theorem should replace assumptions one construct at a time.
Neither a successful Lean build nor a passing differential sample alone changes
the source-level claim.
