# M4 — Strings & Char Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make Haskell `String`/`Char` code transpile faithfully — string literals, `Char` literals, and the safely-mappable slice of `Data.Char` — per the approved spec [2026-07-24-coverage-roadmap-design.md](../specs/2026-07-24-coverage-roadmap-design.md) §M4, with **six spec corrections** established by measurement (below). Final milestone of the roadmap.

**Architecture:** Most of the plumbing already exists — `AST.Literal` has `litString`/`litChar`, `Parse.parseLiteral` handles both, `typeConMap` already sends `[] [Char]` → `List Char`, and `Lower` already erases `C#`. The milestone is therefore narrow and hazard-dense rather than broad: one shim fix unlocks real literal bytes, and that single change makes three latent hazards live at once (no literal escaping; a textual ctor-rewrite pass that reaches inside string literals; an ill-typed `litString` pattern arm). The `Data.Char` surface is small because most of it is unmappable without silent-wrongness.

**Tech Stack:** Lean 4 v4.24.0; GHC 9.2.7 + cabal (`shim/Main.hs` changes → `cd shim && cabal build`); Blaster.

**Branch:** `feature/m4-strings-chars`, stacked on `feature/m3-typeclass-completeness` (PR #5).

---

## Spec corrections (all MEASURED during exploration; these override §M4 where they conflict)

1. **`Parse.lean` needs NO work.** Spec §M4 says "Parse side gains the `LitString` case" — both `LitString` ([Parse.lean:87-89](../../../GhcCoreToLean/Parse.lean)) and `LitChar` (`:90-94`) already exist, as do the AST constructors ([AST.lean:38-39](../../../GhcCoreToLean/AST.lean)). The shim's `LitChar` arm is already present, but **NOT lossless** (review-measured): `text-1.2.5.0`'s `T.singleton` applies `safe`, so `T.singleton '\55296'` yields U+FFFD. Same silent surrogate loss as `MachStr`, latent only because every dump so far has zero `LitChar` — **Task 4** is where a real `Char` literal first appears and must handle it.
   > **AMENDMENT 2 (Task 4, shipped).** The `LitChar` arm's original description in spec §M4 — "already complete and lossless" — was measured FALSE twice over, and is now **FIXED**. `T.singleton` did apply `safe`, and `CharSurrogate.hs` (`lone = '\55296'`) proved it end to end: before the fix, transpile rc=0 and a GREEN `lake build` over `def lone : Char := '\65533'` — a legal, plausible-looking, WRONG `Char`. After, rc=1 with no `.lean` and the refusal ``char literal not representable: code point `U+D800` in bind `lone` ``. The `Char` predicate is deliberately **not** `MachStr`'s: reusing `encodeUtf8 (decodeUtf8With lenientDecode bs) /= bs` would be a guaranteed false negative, since by the time `T.singleton` has run the surrogate is already U+FFFD and U+FFFD round-trips UTF-8 perfectly. The test is on the `Char` itself, before `Text` can destroy it. Parse also reads the flag **before** `value`, which is load-bearing here rather than a future-schema hedge: a flagged `LitChar`'s `value` is an ordinary ONE-character U+FFFD string, so the single-char read would have succeeded and quietly yielded `.litChar '\65533'`.
2. **The `Data.Char` mappable subset is `{isDigit}`, not the spec's seven.** Spec §M4 assumed the hazard was "Haskell `isDigit` is ASCII-only while `isAlpha` is Unicode-aware". Measured on **both** sides (Lean v4.24 `#print` + GHC 9.2.7 execution): Lean is ASCII-only for *all* of them, so the mismatch set is the complement of what was expected. `isAlpha 'é'` → Haskell `True`, Lean `false`; same for `isUpper 'É'`, `isLower 'é'`, `toUpper 'é'`, `toLower 'É'`; `isSpace` differs on `\v`, `\f`, NBSP. **`isDigit` is the only match** (both ASCII 48-57). The other six must stay **unmapped/loud** — a faithful Unicode `isAlpha` needs `base`'s general-category tables, out of scope. The spec's own escape hatch ("mismatch ⇒ `Hs.*` helper or unmapped/loud") authorises this.
3. **`chr` cannot be faithful; leave it unmapped/loud.** Haskell `Char` = [0, 0x10FFFF] **including** the 2048 surrogates; Lean `Char` excludes [0xD800, 0xDFFF]. So the spec's `Hs.chrD` (valid → `Char.ofNat`, invalid → `default`) would map a **defined** Haskell value to a different one — the project's silent-wrong category, *not* the documented ⊥-refinement tradeoff. Measured: `chr 0xD800` is `'\55296'` in Haskell; `Char.ofNat 0xD800` is `'\0'` in Lean. Only `n < 0` and `n ≥ 0x110000` are genuinely ⊥. Also do **not** register `chr` in `isPartialDefaultName` — that flag only affects defs with free type variables, so it's a guaranteed no-op for a monomorphic `Int → Char`.
4. **`ord` is safe** (asymmetry worth stating): every *Lean* `Char` has a faithful Haskell image, so the gap only enters through *construction*. `ord` → `(fun c => (c.toNat : Int))` maps soundly without `chr`.
5. **`min`/`max` on `Char` fail loud** — `Min Char`/`Max Char` do not exist in v4.24 (all other 8 `classConMap "Ord"` binders synthesize at `Char`, plus `Inhabited Char` = `'A'`). Spec §M4's "comparisons/equality reuse the existing `decide`-wrapped Ord path" is true for `<`/`≤`/`==`/`compare`, false for `min`/`max`. Document; do not add instances.
6. **Blaster's `Char` capability is better than the spec's caveat for scalars, and nil for `List Char`.** Measured: `Char` `==`/`<`/`≤`/`compare`/`toNat` and a symbolic `∀ n, n < 128 → (Char.ofNat n).toNat = n` all report `✅ Valid`. But **every** `List Char` goal fails with `Inductive datatype with instance parameters not supported: 'BitVec` — including the `induction`+`blaster` idiom that works at `List Int` (isolated by a byte-identical control). Anything forcing `Char`'s `val : UInt32` representation also fails (`ofNat ∘ toNat`, the `valid` invariant, symbolic `toUpper`). `decide` cannot do `∀ c : Char` (no `Decidable` instance) — only concrete Char data.
   > **AMENDMENT (Task 2, shipped).** "Every `List Char` goal fails" is too strong in one direction: **concrete** `List Char` goals PROVE (`greeting = ['h','i']` and `nameLen greeting = 2` both `✅ Valid`). The claim holds only for goals with a SYMBOLIC list.
   > **AMENDMENT 3 (Task 5, shipped) — the `induction` half is measured FALSE.** "including the `induction`+`blaster` idiom that works at `List Int`" does not hold: the idiom is **goal-dependent at `List Char`**, not uniformly broken. Measured this task (`lake env lean` probes, v4.24.0):
   > * `∀ (cs : List Char), (cs ++ ['!']).length = cs.length + 1` — bare `blaster` fails with the `BitVec` error, but `induction` + `blaster` closes **both** branches (`✅ Valid` ×2). Same for `∀ (cs : List Char), (cs.map Char.toUpper).length = cs.length`.
   > * `StringBasics`'s own `shout_len` (`∀ (cs : List Char), nameLen (shout cs) = nameLen cs + 1`, whose body contains `String.toList "!"`) — bare `blaster` fails, and `induction` + `blaster` closes `nil` but hits the **same** `BitVec` error in `cons`. This is why that fixture proves it by `simp`, and it is the shape a user writing string properties actually hits.
   > So the accurate statement is: **bare `blaster` on a symbolic `List Char` goal fails** (measured on four shapes — the two above plus `cs.reverse.length = cs.length` and one via `String.toList`), while `induction` + `blaster` rescues some goals and not others. The `List Int` control still verifies, so `Char` is the discriminator for the bare case; it is *not* a clean discriminator for the `induction` case. Correction 6's own scalar half is confirmed and EXTENDED: the `Nat → Char → Nat` round-trip verifies even carrying the `Nat → Int` coercion `ord`'s mapping introduces (`CharOps.hs`, 5 `blaster` theorems, all `✅ Valid`).

**Tactic table for M4 fixtures** (measured, use it):

| property shape | tactic |
|---|---|
| concrete string literal + `++`/`length` | `blaster` ✅ or `rfl` ✅ |
| `∀ n, precond → (Char.ofNat n).toNat = n` | `blaster` ✅ |
| Char equality / ordering / `compare` | `blaster` ✅ |
| `∀ (cs : List Char), …` structural law | **`simp`** ✅ (blaster hard-fails) |
| Char `valid`/bounds, `ofNat ∘ toNat`, symbolic `toUpper` | none — avoid or hand-prove |

## Soundness discipline

Loud-fail safe; silent-wrong never. M4 is unusually hazard-dense: **three latent hazards go live the moment the shim emits real bytes**, and two of them are silent. The sequencing in Task 1→2→3 is not stylistic — it is the safety property.

**THE ORDERING CONSTRAINT:** mapping `unpackCString#` *before* the shim fix makes every string literal emit `"<bs>".toList` — type-correct, compiles, silently wrong. The shim fix must land **before or in the same commit as** the mapping.

## Per-task loop

Edit → `lake build GhcCoreToLean` (guards) → (shim changed? `cd shim && cabal build`, and verify the sandbox restaged — a stale plugin/shim silently producing old JSON is this project's classic false-green) → `lake build ghccoretolean` → `./transpile.sh examples/haskell/<Mod>.hs` → `lake build GhcCoreToLean.Generated.<Mod>`.

**Sandbox-flakiness rule (from M4's gate review):** a one-shot regression tally can UNDER-report. Two modules failed the sweep with `no <M>.pass-0000.cbor produced — did the plugin run?` and both transpiled `rc=0` on retry with **no change to any input** — cabal's up-to-date check and the CBOR dump race in a way this pipeline does not control. So **retry any transpile that fails with the missing-cbor message before recording it as red**, and never quote a red from a single run of that shape. (An honest tally distinguishes the two: a real refusal prints a named `error:` line; this one prints the missing-cbor line and nothing else.)

**Gate-evidence rule (from M3's gate review):** `lake build` builds ZERO fixtures — `GhcCoreToLean.lean` does not import `Generated/`. Fixture claims REQUIRE the explicit `lake build GhcCoreToLean.Generated.<F>` loop. Stale `Generated/` artifacts mask emitter regressions; orphaned `.map.json` files with no `.lean` sibling are the tell.

**Byte-identity rule (from M2/M3):** always the two-binary method — build a binary from the parent commit's files, save it, apply the change, run **both** binaries over the **same** saved dumps. Never on-disk snapshot comparison (proven stale). Note `/tmp/transpile-*.json` is swept by OS cleanup; regenerate before measuring.

---

## File Structure

- **Modify** [shim/Main.hs](../../../shim/Main.hs) — `MachStr` emits real bytes (Task 1).
- **Modify** [GhcCoreToLean/Emit.lean](../../../GhcCoreToLean/Emit.lean) — literal escaping; `litString` pattern arm; ctor-rewrite hedge.
- **Modify** [GhcCoreToLean/Maps.lean](../../../GhcCoreToLean/Maps.lean) — `unpackCString#`, `ord`, `isDigit`.
- **Modify** [GhcCoreToLean/Tests/Unit.lean](../../../GhcCoreToLean/Tests/Unit.lean) — per-task `/-! ## M4 Task N -/` sections; **update the stale hedge comment at ~915-926** (Task 3) and the stale `shim/Main.hs:291` line-ref at ~921.
- **Create** `examples/haskell/StringBasics.hs`, `examples/haskell/CharOps.hs`.
- **Modify** [README.md](../../../README.md) — coverage + limitations (final task).
- **Modify** the §M4 spec section — record corrections 1-6 (final task).

---

### Task 1: Shim `MachStr` fix (the prerequisite)

**Files:** `shim/Main.hs`; `GhcCoreToLean/Tests/Unit.lean` (observation block).

Current, [shim/Main.hs:368](../../../shim/Main.hs) — the *only* lossy arm in `convertLit` (the `MachStr bs ->` case; `:324` was accurate when this plan was written and drifted as Task 1's explanation grew):

> **LINE-REF DRIFT, re-measured at Task 5 (final).** Both numbers above are now stale, and no further edit chases them: in the shipped `shim/Main.hs` the `MachStr` arm is at **`:408`** and the `MachChar` arm at **`:366`** (they drifted again as Task 4's `MachChar` refusal and its rationale landed between them). `grep -n 'MachStr\|MachChar' shim/Main.hs` is the durable lookup; treat every `shim/Main.hs:<n>` in this plan as an as-written marker, not a current address. The `Unit.lean:915-926` hedge comment and its `shim/Main.hs:291` ref were fixed by Task 3 — `grep` confirms no `:291` or bare `:324` assertion survives in `Tests/Unit.lean`.
```haskell
  MachStr _     -> object [ "tag" .= ("LitString" :: T.Text), "value" .= ("<bs>" :: T.Text) ]
```
Upstream is lossless (`GhcDump/Convert.hs:265-266` → `Ast.MachStr BS.ByteString`, strict), so the real bytes already reach the shim.

- [x] **Step 1:** Emit the actual bytes, UTF-8 decoded with a **replacement** decoder (not a partial one — a malformed byte must not crash the shim). `bytestring`/`text` are already in `shim.cabal`; `Main.hs:5-6` imports only the Lazy modules, so add e.g. `Data.Text.Encoding (decodeUtf8With)` + `Data.Text.Encoding.Error (lenientDecode)` + strict `Data.ByteString`. No cabal change.
- [x] **Step 2: Observation fixture.** Create `examples/haskell/StringBasics.hs` with just a literal-bearing def for now (`greeting :: String; greeting = "hi"`) plus a second literal containing hazardous characters (`quoted = "say \"hi\"\n"` — a quote, a backslash-escape, a newline). Rebuild shim, confirm sandbox restaged, transpile. **QUOTE** the JSON for both literals, and the `unpackCString#` spine. Note the census: `LitString` appears in **all** dumps (2-54 per dump) but exclusively inside `$tr`/`$tc` Typeable binds that `isJunkName` drops — so this task's blast radius is exactly those dropped binds plus any new value-position literal. Verify that claim still holds post-fix.
- [x] **Step 3:** `lake build ghccoretolean` and re-transpile 3-4 corpus fixtures. Because the bytes now differ inside dropped binds, emitted output should be **byte-identical** (the binds are dropped before emission) — verify, since a diff here means a Typeable bind is reaching emission.
- [x] **Step 4: Commit** (`fix(shim): emit real string-literal bytes (MachStr was discarding payloads)`).

### Task 2: String literals — `unpackCString#` + escaping

**Files:** `GhcCoreToLean/Maps.lean`, `GhcCoreToLean/Emit.lean`, `GhcCoreToLean/Tests/Unit.lean`, `examples/haskell/StringBasics.hs`.

Two changes that MUST land together (either alone is broken):

- [x] **Step 1 — escaping.** [Emit.lean:134-135](../../../GhcCoreToLean/Emit.lean) interpolates raw, with **no escaping anywhere** (`sanitize`/`sanitizeChar` apply to *names* only):
  ```lean
    | .litString s => s!"\"{s}\""
    | .litChar c   => s!"'{c}'"
  ```
  Today that's harmless only because the payload is always the literal `<bs>`. Post-Task-1, a `"`/`\`/newline produces unparseable Lean. Add escaping for `.litString` (`\`, `"`, control chars) and `.litChar` (`\`, `'`, control chars) — or emit char literals as `Char.ofNat n` to sidestep quoting entirely (your call; report which and why). Guards over the hazardous set from Task 1's fixture, including a literal that is exactly `"` and one containing `\n`.
- [x] **Step 2 — the mapping.** Core spells a literal `GHC.CString.unpackCString# "lit"#`; `unpackCString#` is absent from `valueMap` (verified: `emitVar` falls through to `refId` → `qualifyName` → `GHC.CString.unpackCString_hash_`, a loud unknown identifier). Map it so a literal emits `"lit".toList` — the `.toList` is **load-bearing**: a bare Lean `"lit"` elaborates as `String`, not `List Char`, so the `.litString` arm alone gives an ill-typed term where `List Char` is expected. **`unpackCStringUtf8#` is REQUIRED, not a hedge** (Task 1 measured: GHC picks plain `unpackCString#` only for pure-ASCII literals and the Utf8 variant for *every* non-ASCII one — `"caf\233"`, `"\255"`, `"\128169"` all take it). Map both or every accented string fails loud. Observe the actual names in the dump first and record negatives.

- [x] **Step 2b — `typeConMap "String"` (new, Task 1 finding).** Core keeps the SYNONYM in binder types (`{"tag":"TyCon","name":"String","args":[]}`), so a `String` binder emits `(GHCCore.tyConOpaque "String")`. Correction 1's "`[] [Char]` already maps" is true but does not cover this spelling. Add the arm; guard is already staged as a tripwire.

- [x] **Step 2c — lossy-decode refusal (new, REQUIRED; Task 1 finding).** GHC emits *modified* UTF-8 (overlong NUL `C0 80`, 3-byte lone surrogates — NOT CESU: non-BMP chars use standard 4-byte UTF-8), so the shim's lenient decode turns `"a\0b"` (3 chars) into 4 code points with two U+FFFD. Mapping the unpackers **replaces a loud failure with a silently-wrong value**. The predicate `encodeUtf8 (decodeUtf8With lenientDecode bs) /= bs` is a *sound* lossiness test (audited both directions in the `M4 Task 1` Unit.lean block) but **coarse as a refusal**: split it — U+0000 is a legal Lean `Char` and deserves faithful support (a modified-UTF-8-aware decode), while only U+D800–DFFF is genuinely unrepresentable (correction 3) and must refuse. **The predicate is computable ONLY in the shim** (bytes are gone after JSON), so this needs a shim-emitted JSON flag field plus a Lean-side refusal; it cannot be recomputed in Lean. Refuse in Lean rather than dying in the shim, because the shim cannot know whether a literal reaches emission — a shim-level `die` would crash modules whose only lossy literal sits in a dropped bind.
- [x] **Step 3 — the pattern arm.** [Emit.lean:143](../../../GhcCoreToLean/Emit.lean) `emitLiteralPattern | .litString s => s!"\"{s}\""` would be **ill-typed** against a `List Char` scrutinee. Measured: `LitChar ×0` and no value-position `LitString` in any of 35 dumps, so the arm is entirely unobserved. Determine whether GHC can emit `LitAlt (MachStr …)` at all (Haskell string patterns normally desugar to `==` on lists); if it can't be ruled out, make the arm **fail loud** rather than emit an ill-typed pattern. `.litChar` in pattern position is fine (`'c'` against a `Char` scrutinee).
- [x] **Step 4 — fixture + e2e.** Grow `StringBasics.hs`: literals, `++`, `length`, a `String -> Int` function (note `f s = length s` already works today — the type path is sound, only literal *production* was broken). Properties per the tactic table: `blaster`/`rfl` for concrete, `simp` for `∀ (cs : List Char)`. Verify; two-binary byte-identity over the corpus.
- [x] **Step 5: Commit** (`feat(strings): string literals via unpackCString# + literal escaping`).

### Task 3: Re-guard the ctor-rewrite hedge (it goes live here)

**Files:** `GhcCoreToLean/Emit.lean`, `GhcCoreToLean/Tests/Unit.lean`.

[Tests/Unit.lean:915-926](../../../GhcCoreToLean/Tests/Unit.lean) documents a known hedge: `resolveUserCtors`/`replaceCtorApps` are **textual**, so a ctor name followed by args inside a string literal gets rewritten. Its safety argument is *"no Haskell string literal can reach the emitter at all"* — which **evaporates the moment Task 1 lands**. After it, a Haskell literal `"Point (1)"` emits as `"Point.Point (1)".toList`: silently wrong, and no longer confined to hand-authored spec text.

- [x] **Step 1:** Reproduce it — a fixture with a data type `Point` and a string literal containing `Point (1)`. Confirm the rewrite fires and is silent (quote pre-state).
- [x] **Step 2:** Fix by skipping rewrites inside string literals (a literal-aware scan in `replaceCtorApps` and the four needles in `resolveUserCtors`, `Emit.lean:3545`/`3581-3592`). Watch the interaction with Task 2's escaping — an escaped `\"` inside a literal must not end the literal for the scanner. Guards both directions (rewrites outside literals still fire; inside literals never).
- [x] **Step 3:** Update the stale comment at `Unit.lean:915-926` (its premise is now false) and the stale `shim/Main.hs:291` ref at `:921` (the arm is at `:368`). Promote the probe to a committed fixture if it's ordinary Haskell.
- [x] **Step 4: Commit** (`fix(strings): ctor rewrites skip string literals (silent-wrong once literals are real)`).

### Task 4: `Char` operations

**Files:** `GhcCoreToLean/Maps.lean`, `GhcCoreToLean/Tests/Unit.lean`, `examples/haskell/CharOps.hs`.

- [x] **Step 1: Fixture-first.** `CharOps.hs`: `Char` literals, equality/ordering, `ord`, `isDigit`, and a `Nat → Char → Nat` round-trip with an explicit non-surrogate precondition (that shape verifies with `blaster` — measured). QUOTE the observed Core names for `ord`/`isDigit` (expect `Data.Char.*` or `GHC.Char.*` — hedge both per the observed-names discipline) and confirm `C#` erasure works on a real `Char` literal (`Lower.lean:33,50-52` — the path exists but has never seen a `LitChar`, since all 35 dumps had zero).
- [x] **Step 2: Map only what's safe** — `ord` → `(fun c => (c.toNat : Int))`; `isDigit` → `Char.isDigit`. Add semantic pins (`isDigit` on `'0'`,`'9'`,`'a'`,`'A'`, and the ARABIC-INDIC `'٥'` U+0665 which is `False` on both sides).
- [x] **Step 3: Loud-fail boundary guards** (this is the task's soundness core — pin what must NOT be mapped, with the reason, so a future contributor has to face the measurement rather than "helpfully" adding them):
  ```lean
  -- Lean v4.24 is ASCII-only for these; Haskell is Unicode-aware. Measured
  -- both sides: isAlpha 'é' = True (Haskell) / false (Lean), etc. Mapping any
  -- of them would be SILENT-WRONG. chr is worse: Haskell's Char includes the
  -- 2048 surrogates, Lean's does not, so no total Lean function is faithful.
  #guard valueMap "Data.Char.isAlpha" == none
  #guard valueMap "Data.Char.isUpper" == none
  #guard valueMap "Data.Char.isLower" == none
  #guard valueMap "Data.Char.toUpper" == none
  #guard valueMap "Data.Char.toLower" == none
  #guard valueMap "Data.Char.isSpace" == none
  #guard valueMap "Data.Char.chr"     == none
  ```
  (Hedge the qualification the same way — if the dump shows `GHC.Unicode.*`, pin those keys too.)
- [x] **Step 4:** e2e per the tactic table; two-binary byte-identity. Note `min`/`max` at `Char` fail loud (correction 5) — don't put them in the fixture except as a documented negative if cheap.
- [x] **Step 5: Commit** (`feat(chars): ord + isDigit; loud-fail pins for the unmappable Data.Char surface`).

### Task 5: README + spec corrections + full regression + gate

**Files:** `README.md`, the §M4 spec section, `docs/superpowers/plans/` (this file's checkboxes).

- [x] **Step 1: README.** Add: `String`/`[Char]` → `List Char` with working literals; `Char` literals, equality/ordering, `ord`, `isDigit`. Limitations, each verified before writing: `chr` unmapped (surrogate gap — Haskell's `Char` has 2048 code points Lean's cannot represent); the six Unicode-vs-ASCII `Data.Char` functions unmapped; `min`/`max` at `Char` loud; **and the verification caveat** — Blaster handles `Char` scalars but **no** `List Char` goal (a `BitVec` encoding limit), so string properties need `simp`/`rfl` and `decide` cannot quantify over `Char`.
- [x] **Step 2: Spec corrections.** Record corrections 1-6 in the §M4 spec section so the design doc stops asserting measured-false things (the project's docs are load-bearing evidence for later work).
- [x] **Step 3: Full regression**, collect-don't-break, per the gate-evidence rule. Expected reds: `UserClass` (pre-existing false theorem — report, don't fix, unless the user has fixed it) and the SEVEN must-fail fixtures (`NewtypeInstances`, `UserClassNeqWithEq`, `UserClassEqWithEq`, `TwoClassesSameMethod`, and M4's own `StringSurrogate`, `CharSurrogate`, `SpecInterp` — the last added by the gate review, for the spec-text desync refusal). Keep this list CURRENT: an unlisted red is indistinguishable from a regression, which is the same tally failure the rule above is about. Count ✅ Valid, **deduplicating by owning file** — cross-module builds replay imported modules' ✅ lines (M3's Task 8 found a naive sum inflated 74 → 81).
- [ ] **Step 4: Commit** docs, then gate: whole-branch review subagent → `gh pr create` (base `feature/m3-typeclass-completeness`) → user checkpoint.

---

## Self-review notes

- Spec §M4 coverage: shim fix (T1); String = `List Char` + literals (T2); Char literals + `ord`/`isDigit`/`chr`-decision (T4); fixtures `StringBasics`/`CharOps` (T2, T4); README + the documented verification caveat (T5). The spec's own `Hs.chrD` and 7-predicate list are **deliberately not implemented** — corrections 2 and 3 explain why, with measurements.
- T3 exists only because T1 makes a documented hedge live; it has no spec line of its own. Skipping it would ship a silent-wrong, so it is not optional.
- The escaping work (T2 Step 1) and the literal-aware ctor scan (T3 Step 2) interact — flagged inline.
- No task depends on Blaster gaining `List Char` support; the tactic table routes around it.
