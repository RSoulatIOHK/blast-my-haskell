{-# OPTIONS_GHC -fplugin GhcDump.Plugin #-}
-- NEGATIVE fixture: transpilation MUST fail. `./transpile.sh
-- examples/haskell/UserClassEqWithEq.hs` is expected to exit 1 with an error
-- naming `==`, the head `R`, and BOTH candidate classes (`Eq` and `MyEq`), and to
-- produce no GhcCoreToLean/Generated/UserClassEqWithEq.lean. Deliberately
-- EXCLUDED from the green-regression list, like NewtypeInstances.hs,
-- TwoClassesSameMethod.hs and UserClassNeqWithEq.hs.
--
-- THE SILENT-WRONG THIS PINS, and it was measured on this exact module before the
-- refusal existed. `UserClassNeqWithEq.hs` covers the `/=` cell of this family:
-- both `$c/=` binds are DROPPED, the method→class map loses its entry, and
-- `Emit.unmappedOperatorMethods` refuses. The `==` cell is NOT that shape — no
-- bind is dropped, both survive, the map entry is present — and so it reached
-- neither existing guard:
--
--   * `Emit.sameMethodAmbiguities` builds its class set from the plugin-dumped ∪
--     Core-reconstructed USER classes, so the builtin `Eq` is not in it and `==`
--     looks singly-declared.
--   * `Emit.unmappedOperatorMethods` requires the method to be ABSENT from the
--     method map; `MyEq` has a local instance, so `==` is present.
--
-- GHC emits TWO binds named `$c==`, both typed `R -> R -> Bool` — one per
-- instance, distinguishable only by unique. `Emit.findClassMethodBind` keyed on
-- `(method name, first value-argument type)` and took the FIRST, so the `Eq`
-- route wired the USER class's body. OBSERVED (rc=0, empty stderr):
--
--     def _dollar_c_eq__eq__2948 (ds : R) (ds : R) : Bool :=   -- MyEq's `a > c`
--     def _dollar_c_eq__eq__2931 (ds : R) (ds : R) : Bool :=   -- derived, structural
--
--     instance : BEq R where
--       beq := _dollar_c_eq__eq__2948          -- the USER class's body
--
--     def structEq (x : R) (y : R) : Bool := ((· == ·) x) y
--
-- with `_dollar_c_eq__eq__2931` emitted and never referenced (the dead-code
-- tell). `structEq` in Haskell is DERIVED structural equality; the emitted Lean
-- computes `a > c`. Both directions were confirmed with `lake env lean`:
--
--     #eval structEq (R 2 0) (R 1 0)   -- Lean: true    Haskell: False
--     #eval structEq (R 1 5) (R 1 5)   -- Lean: false   Haskell: True
--     theorem … structEq (R 2 0) (R 1 0) = false := by decide
--       ⇒ "Tactic `decide` proved that the proposition … is false"
--
-- `decide` proving a Haskell falsehood with no diagnostic anywhere is the one
-- failure mode this project forbids, so the program is refused
-- (`Emit.ambiguousMethodBinds`, wired in `Main.lean`).
--
-- WHAT EACH PART IS LOAD-BEARING FOR:
--
--   * A PLAIN `import Prelude` — no `hiding` pragma. Declaring `(==)` in a class
--     is legal with `Prelude.(==)` in scope; only unqualified USES are ambiguous,
--     and every use here is qualified. This is what makes the shape ordinary
--     Haskell rather than an artifact of `hiding`.
--   * `deriving Prelude.Eq` on `R`, giving the SECOND `$c==` at head `R`.
--   * `R` carrying FIELDS. A derived `==` over fields compares them with `eqInt`
--     and uses no tag primops, so `Emit.derivedEqTypes` does not classify head
--     `R` as derived and the `Eq` instance takes the hand-written route — which is
--     the route that consults `findClassMethodBind`. THE FIELDLESS VARIANT IS A
--     DIFFERENT, ALREADY-LOUD CELL, and the difference is measured rather than
--     argued (probe: `class MyEq a where (==)` + `data E = A | B deriving
--     Prelude.Eq` + `instance MyEq E` + `structEq x y = x Prelude.== y`). A
--     nullary-constructor enum's derived `==` IS tag-based, so head `E` lands in
--     `derivedEqTypes` and `isSuppressedMethod` — name+head keyed, so it cannot
--     tell the two binds apart either — suppresses BOTH. At HEAD that emitted,
--     rc=0 and empty stderr, an `instance : MyEq E` pointing at a def that no
--     longer exists:
--
--         instance : MyEq E where
--           _eq__eq_ := _dollar_c_eq__eq__2951      -- never defined
--
--     which `lake build` rejects with `Unknown identifier
--     _dollar_c_eq__eq__2951`. `structEq` there was CORRECT (the `deriving
--     DecidableEq` the derived route adds supplies the structural `BEq`), so that
--     cell was loud-and-incomplete, never silently wrong. The fields on `R` are
--     what move the `Eq` instance onto the hand-written route and make the wrong
--     body reachable. Both cells are refused now, by the same check — the two
--     `$c==` binds are in `p.binds` whatever `isSuppressedMethod` later does with
--     them — and for this one that is a strict diagnostic improvement over a
--     mangled `Unknown identifier`.
--   * `structEq` using `Prelude.==`, i.e. a call site that must mean the DERIVED
--     equality. Without a use of the builtin operator at this head there is no
--     wrong answer to compute.
--   * The instance body is deliberately NOT equality (`a > c`), so the two
--     semantics are distinguishable at all.
--
-- The refusal names both classes because the instance DICTIONARIES do carry the
-- attribution (`$fEqR = GHC.Classes.C:Eq @R $c==(2931) $c/=(2940)`,
-- `$fMyEqR = $c==(2948)`) — `Emit.dictMethodRefs` reads it. Emitting CORRECTLY off
-- that attribution is a larger change than this refusal: see the "Two
-- `$c<method>` binds at one head" section header in Emit.lean for the four
-- independent head-only decision points that would all have to agree.
module UserClassEqWithEq where
    import Prelude

    class MyEq a where
        (==) :: a -> a -> Bool

    data R = R Int Int deriving Prelude.Eq

    instance MyEq R where
        (R a _) == (R c _) = a Prelude.> c

    structEq :: R -> R -> Prelude.Bool
    structEq x y = x Prelude.== y
