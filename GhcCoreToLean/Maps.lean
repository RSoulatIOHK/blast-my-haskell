import GhcCoreToLean.AST

namespace GHCCore.Maps

/-- GHC global Id / class method names → Lean term to splice into emitted source.
    Both fully-qualified GHC names and bare operator forms are accepted. -/
def valueMap : String → Option String
  | "GHC.Num.+"     | "+"  => some "(· + ·)"
  | "GHC.Num.-"     | "-"  => some "(· - ·)"
  | "GHC.Num.*"     | "*"  => some "(· * ·)"
  | "GHC.Num.negate"| "negate" => some "Neg.neg"
  | "GHC.Num.abs"   | "abs" => some "(fun a => if a < 0 then -a else a)"
  -- Integral division. Haskell `quot`/`rem` truncate toward zero (Lean
  -- `Int.tdiv`/`Int.tmod`); `div`/`mod` floor (Lean `Int.fdiv`/`Int.fmod`).
  | "GHC.Real.quot" | "quot" => some "Int.tdiv"
  | "GHC.Real.rem"  | "rem"  => some "Int.tmod"
  | "GHC.Real.div"  | "div"  => some "Int.fdiv"
  | "GHC.Real.mod"  | "mod"  => some "Int.fmod"
  -- Haskell's comparison operators return `Bool`. Lean 4's `≤`/`<`/etc. return
  -- `Prop`, so we wrap them in `decide` to get Bool back. `==` is already Bool
  -- via the `BEq` instance, so it does not need wrapping.
  | "GHC.Classes.=="| "==" => some "(· == ·)"
  | "GHC.Classes./="| "/=" => some "(fun a b => !(a == b))"
  | "GHC.Classes.<" | "<"  => some "(fun a b => decide (a < b))"
  | "GHC.Classes.<=" | "<=" => some "(fun a b => decide (a ≤ b))"
  | "GHC.Classes.>" | ">"  => some "(fun a b => decide (a > b))"
  | "GHC.Classes.>=" | ">=" => some "(fun a b => decide (a ≥ b))"
  -- Prelude `min`/`max` (Ord methods) → Lean's. Only the *qualified* Prelude
  -- names are mapped, never bare `min`/`max`: a user's own `min`/`max` def is a
  -- bare Core name and must keep resolving to that local def, not be hijacked.
  | "GHC.Classes.min" => some "Min.min"
  | "GHC.Classes.max" => some "Max.max"
  -- Bottoms. Applied forms are collapsed to `sorry` in Emit (spine-head
  -- check); this covers the rare bare/unapplied reference.
  | "GHC.Err.error" | "error"
  | "GHC.Err.errorWithoutStackTrace" | "errorWithoutStackTrace"
  | "GHC.Err.undefined" | "undefined" => some "sorry"
  | "GHC.Base.id"          => some "id"
  | "GHC.Base.."           => some "Function.comp"
  -- GHC's True/False are data constructors used in value positions. Map them
  -- to Lean's Bool literals so dict-method bodies like `$c/=` compile.
  | "GHC.Types.True"       => some "true"
  | "GHC.Types.False"      => some "false"
  -- List library (total). Haskell `++`/`map`/… map directly to Lean `List.*`.
  -- `foldr`/`foldl` are eta-wrapped so their Haskell arg order (f, z, xs) is
  -- pinned explicitly. As with `min`/`max` above, bare *alphabetic* forms are
  -- intentionally omitted: a user's own top-level `map`/`filter`/`length`/… def
  -- is a bare Core name and must keep resolving to that local def, not be
  -- hijacked here. Core qualifies these names anyway, so nothing is lost. Bare
  -- *operator* forms (`++`, `&&`, …) stay, since users can't shadow them.
  | "GHC.Base.++"      | "++"      => some "List.append"
  -- List literals. `[a,b,x3]` desugars to `GHC.Base.build (\c n -> c a (c b (c x3 n)))`
  -- where `build g = g (:) []` (Lower erases both the rank-2 type application
  -- AND the type binder on g). `augment g xs = g (:) xs` is introduced by the
  -- "++" RULE in simplifier passes ≥ 1, which the pass-0000 dump this pipeline
  -- reads never reaches — the arm is a forward hedge in case the dump point
  -- moves, NOT a live `++` path (observed: 0 occurrences at pass-0000).
  | "GHC.Base.build"   => some "(fun g => g List.cons List.nil)"
  | "GHC.Base.augment" => some "(fun g xs => g List.cons xs)"
  | "GHC.Base.map"                => some "List.map"
  | "GHC.List.filter"             => some "List.filter"
  | "GHC.List.reverse"            => some "List.reverse"
  -- Int ranges (Enum dict is erased by Lower). `enumFrom`/`enumFromThen`
  -- (infinite) are intentionally NOT mapped — loud fail.
  | "GHC.Enum.enumFromTo"     => some "Hs.enumFromTo"
  | "GHC.Enum.enumFromThenTo" => some "Hs.enumFromThenTo"
  -- Int-indexed list ops. Haskell clamps negative counts to "empty/unchanged";
  -- `Int.toNat` clamps negatives to 0 — the semantics match exactly.
  | "GHC.List.take"      => some "(fun n xs => List.take n.toNat xs)"
  | "GHC.List.drop"      => some "(fun n xs => List.drop n.toNat xs)"
  | "GHC.List.splitAt"   => some "Hs.splitAt"
  | "GHC.List.replicate" => some "(fun n x => List.replicate n.toNat x)"
  -- Zip family. Eta-wrapped for arity legibility ONLY — these lambdas are
  -- definitionally equal to the bare names and pin nothing; arg order is
  -- pinned by the (· - ·) guards in Tests/Unit.lean, the only thing that
  -- catches a flip. Truncation to the shorter list matches Haskell.
  | "GHC.List.zip"     => some "(fun xs ys => List.zip xs ys)"
  | "GHC.List.zipWith" => some "(fun f xs ys => List.zipWith f xs ys)"
  -- Asymmetry is deliberate: only `unzip` carries a `Data.List` hedge, because
  -- the M1 plan mandated exactly that key. `zip`/`zipWith` were observed as
  -- `GHC.List.*` only and the plan lists no hedge for them, so none is added.
  | "GHC.List.unzip" | "Data.List.unzip" => some "List.unzip"
  -- Foldable methods (post-FTP). The desugarer resolves these through
  -- `Data.Foldable.*` on `[a]`, NOT `GHC.List.*` — include both forms so the
  -- mapping fires regardless of which name appears.
  -- Haskell `length` returns `Int`; Lean `List.length` returns `Nat`. Coerce
  -- to `Int` (like `gcd`/`lcm`) so it composes with Int arithmetic.
  | "Data.Foldable.length" | "GHC.List.length"  => some "(fun xs => (List.length xs : Int))"
  | "Data.Foldable.null"   | "GHC.List.null"    => some "List.isEmpty"
  -- `GHC.Base.foldr` is the third alternative because list COMPREHENSIONS
  -- desugar through it, not through the Foldable method: `[2*x | x <- xs]`
  -- becomes `build (\c n -> GHC.Base.foldr (\ds ds' -> c (2*ds) ds') n xs)`.
  -- It is the list-specialised `foldr :: (a->b->b) -> b -> [a] -> b` — two
  -- type args then `(f) (z) (xs)` and NO dict (observed in the JSON), so it
  -- has the same shape as the dict-erased Foldable form and shares this arm.
  -- The foldl arm below has no matching `GHC.Base.*` alternative on purpose:
  -- `GHC.Base` exports `foldr` (it is the fusion partner of `build`, which is
  -- why comprehensions desugar to it) but exports no `foldl` at all — checked
  -- against GHC 9.2.7, where `import GHC.Base (foldl)` is a hard export error.
  | "Data.Foldable.foldr"  | "GHC.List.foldr" | "GHC.Base.foldr"
                                               => some "(fun f z xs => List.foldr f z xs)"
  | "Data.Foldable.foldl"  | "GHC.List.foldl"   => some "(fun f z xs => List.foldl f z xs)"
  -- Folds & predicates (Foldable methods post-FTP; GHC.List hedged).
  -- sum/product are hand-rolled as explicit foldl for two concrete reasons:
  -- (a) v4.24 core has NO `List.product` whatsoever, so `product` must be
  -- hand-rolled regardless, and symmetry argues for hand-rolling `sum` too;
  -- (b) core's `List.sum` is `foldr (· + ·) 0` while GHC's is `foldl (+) 0`,
  -- so the explicit foldl is the more faithful image of the source.
  -- The all/any wraps are LOAD-BEARING adapters (Haskell arg order is (p, xs);
  -- Lean's List.all/any take the list first) — not legibility wraps.
  | "Data.Foldable.sum"     | "GHC.List.sum"     => some "(fun xs => List.foldl (· + ·) 0 xs)"
  | "Data.Foldable.product" | "GHC.List.product" => some "(fun xs => List.foldl (· * ·) 1 xs)"
  | "Data.Foldable.all"     | "GHC.List.all"     => some "(fun p xs => List.all xs p)"
  | "Data.Foldable.any"     | "GHC.List.any"     => some "(fun p xs => List.any xs p)"
  | "Data.Foldable.and"     | "GHC.List.and"     => some "Hs.and"
  | "Data.Foldable.or"      | "GHC.List.or"      => some "Hs.or"
  -- Search & flatten. elem/notElem/lookup are Eq-constrained; the project's
  -- image of Haskell `Eq` is `BEq` (hand-written Eq instances become BEq
  -- instances), which is exactly what Lean's `List.contains`/`List.lookup`
  -- require. The elem/notElem/lookup wraps are LOAD-BEARING adapters, not
  -- legibility wraps: Haskell's arg order is (x, xs) / (k, ps) with the
  -- searched-for value FIRST, whereas Lean's `List.contains`/`List.lookup` are
  -- reached receiver-first via dot notation. `concat` needs no wrap
  -- (`List.flatten : List (List α) → List α` is already point-free-compatible);
  -- `concatMap` does, since Haskell's is (f, xs).
  | "Data.Foldable.elem"    | "GHC.List.elem"    => some "(fun x xs => xs.contains x)"
  | "Data.Foldable.notElem" | "GHC.List.notElem" => some "(fun x xs => !(xs.contains x))"
  | "GHC.List.lookup"       | "Data.List.lookup" => some "(fun k ps => ps.lookup k)"
  | "Data.Foldable.concat"  | "GHC.List.concat"  => some "List.flatten"
  | "Data.Foldable.concatMap" | "GHC.List.concatMap" => some "(fun f xs => xs.flatMap f)"
  -- Boolean / Prelude combinators.
  | "GHC.Classes.&&"   | "&&"      => some "(· && ·)"
  | "GHC.Classes.||"   | "||"      => some "(· || ·)"
  | "GHC.Classes.not"             => some "not"
  | "GHC.Base.const"              => some "(Function.const _)"
  | "GHC.Base.flip"               => some "(fun f a b => f b a)"
  | "GHC.Base.$"       | "$"       => some "(fun f x => f x)"
  | "GHC.Base.otherwise"          => some "true"
  -- Partial functions. Haskell `head`/`last`/`!!`/`fromJust` are ⊥ ONLY on the
  -- empty list / `Nothing`; they are faithful on the rest of their domain. So
  -- they must NOT collapse to `default` everywhere (that breaks the defined
  -- domain, e.g. `head [1,2,3]`). We map to Lean's total `*D`/`getD` forms:
  -- faithful where Haskell is defined, and `default` (an arbitrary inhabitant)
  -- exactly where Haskell is ⊥ — the documented partial-correctness tradeoff.
  -- `default` needs `[Inhabited t]`, which `emitDefHeader` adds for polymorphic
  -- defs (Emit recognises these names via `isPartialDefaultName`). `tail`/`init`
  -- map to Lean totals that need no default. Qualified only (don't shadow a
  -- user's own `head`/`tail`/… def).
  | "GHC.List.head"       => some "(fun xs => xs.headD default)"
  | "GHC.List.tail"       => some "List.tail"
  | "GHC.List.init"       => some "List.dropLast"
  | "GHC.List.last"       => some "(fun xs => xs.getLastD default)"
  | "GHC.List.!!"         => some "(fun xs i => xs.getD i.toNat default)"
  | "Data.Maybe.fromJust" => some "(fun m => m.getD default)"
  -- Tuple projections. Qualified only (a user could define `fst`/`snd`); the
  -- desugarer resolves these through `Data.Tuple.*`.
  | "Data.Tuple.fst"              => some "Prod.fst"
  | "Data.Tuple.snd"              => some "Prod.snd"
  -- Num / Integral / Ord completion. Qualified names only (no bare alphabetic
  -- forms), so a user's own `signum`/`divMod`/… top-level def is not hijacked.
  -- Integer/Int are both Lean `Int`, so the coercion methods are identities.
  | "GHC.Num.fromInteger"   => some "id"
  | "GHC.Real.toInteger"    => some "id"
  | "GHC.Real.fromIntegral" => some "id"
  | "GHC.Num.signum"        => some "(fun a => if a < 0 then -1 else if a > 0 then 1 else 0)"
  -- divMod floors (fdiv/fmod); quotRem truncates (tdiv/tmod). Returns a pair.
  | "GHC.Real.divMod"       => some "(fun a b => (Int.fdiv a b, Int.fmod a b))"
  | "GHC.Real.quotRem"      => some "(fun a b => (Int.tdiv a b, Int.tmod a b))"
  -- Lean `Int.gcd`/`Int.lcm` return `Nat`; Haskell returns the numeric type.
  | "GHC.Real.gcd"          => some "(fun a b => (Int.gcd a b : Int))"
  | "GHC.Real.lcm"          => some "(fun a b => (Int.lcm a b : Int))"
  | "GHC.Classes.compare"   => some "compare"
  -- Unboxed Int# primops. Arithmetic maps to boxed ops (I#/Int# both → Int);
  -- comparisons mirror the GHC.Classes.* `decide`-wrapped Bool forms.
  | "GHC.Prim.+#"  => some "(· + ·)"
  | "GHC.Prim.-#"  => some "(· - ·)"
  | "GHC.Prim.*#"  => some "(· * ·)"
  | "GHC.Prim.==#" => some "(· == ·)"
  | "GHC.Prim./=#" => some "(fun a b => !(a == b))"
  | "GHC.Prim.<#"  => some "(fun a b => decide (a < b))"
  | "GHC.Prim.<=#" => some "(fun a b => decide (a ≤ b))"
  | "GHC.Prim.>#"  => some "(fun a b => decide (a > b))"
  | "GHC.Prim.>=#" => some "(fun a b => decide (a ≥ b))"
  -- Maybe/Either eliminators (total). Confirmed v4.24.0 signatures:
  --   `Option.elim : Option α → β → (α → β) → β`   (scrutinee FIRST), so
  --   Haskell `maybe d f m` ≡ `Option.elim m d f`.
  --   `Sum.elim : (α → γ) → (β → γ) → α ⊕ β → γ`   (scrutinee LAST), so
  --   Haskell `either f g e` ≡ `Sum.elim f g e`.
  --   `fromMaybe d m` ≡ `Option.getD m d`.
  | "GHC.Maybe.maybe"      => some "(fun d f m => Option.elim m d f)"
  | "Data.Maybe.fromMaybe" => some "(fun d m => Option.getD m d)"
  | "Data.Maybe.isJust"    => some "Option.isSome"
  | "Data.Maybe.isNothing" => some "Option.isNone"
  | "Data.Either.either"   => some "(fun f g e => Sum.elim f g e)"
  | _                      => none

/-- Parenthesize an already-emitted type string for APPLICATION-ARGUMENT
    position. Needed by the arms below that splice their args by juxtaposition
    (`List a`, `Option a`, `Sum a b`): without it, `[[Int]]` emits the ill-typed
    `List List Int`. The defect is wider than nested lists — `Maybe [Int]` gave
    `Option List Int` and `[Maybe Int]` gave `List Option Int`. Earlier M1
    fixtures dodged it by only using `[Int]`, `[(Int, Int)]` and tuples-of-lists
    (safe because `×` is `infixr:35`, BELOW application, so `List Int × Int`
    already parses as `(List Int) × Int` — which is why the tuple arms below
    need no `parenArg`).

    The `!startsWith "("` test rests on an invariant of `Emit.emitType`, whose
    producers are a closed set, in three buckets:
    * ATOMIC (space-free): tyVar, nat literal, and MAPPED nullary tyCon. Note
      "nullary tyCon ⇒ atomic" holds only for the MAPPED ones — every nullary
      arm below returns a single word (Int / Nat / Bool / Char / Unit /
      Ordering).
    * FULLY BRACKETED: tyFun `(a → r)`, tyApp `(f x)`, forAll `(∀ …)`, the
      tuple arms `(a × b)`, and BOTH opaque-tyCon shapes — the applied
      `((GHCCore.tyConOpaque "T") (a))` and the NULLARY
      `(GHCCore.tyConOpaque "T")`. The latter DOES contain a space, so it
      belongs in this bucket rather than with the atoms; being bracketed, it is
      correctly left alone.
    * SPACE-CONTAINING and UNBRACKETED: the four juxtaposition arms below — the
      case `parenArg` exists for — plus one benign outlier, a string type
      literal `.tyLit (.str s)` whose payload has a space, which emits `"a b"`
      and so gets wrapped to `("a b")`. Harmless: parens around a literal are
      inert.
    So a leading `(` still implies fully bracketed, and the juxtaposition arms
    are the only place the wrapping is load-bearing. A future arm that splices
    args by juxtaposition must use `parenArg` too; one that emits a new
    space-containing UNBRACKETED shape in which parens are NOT inert would
    break this invariant. -/
private def parenArg (s : String) : String :=
  if s.contains ' ' && !s.startsWith "(" then s!"({s})" else s

/-- GHC type constructor name + args → Lean type expression (as a string,
    with arg strings already emitted). Returns `none` when the ctor is opaque. -/
def typeConMap : String → List String → Option String
  | "Int",     []     => some "Int"
  | "Int#",    []     => some "Int"
  | "GHC.Prim.Int#", [] => some "Int"
  | "Integer", []     => some "Int"
  | "Word",    []     => some "Nat"
  | "Word#",   []     => some "Nat"
  | "GHC.Prim.Word#", [] => some "Nat"
  | "Bool",    []     => some "Bool"
  | "Char",    []     => some "Char"
  | "Char#",   []     => some "Char"
  | "GHC.Prim.Char#", [] => some "Char"
  | "()",      []     => some "Unit"
  -- Juxtaposition arms — args go through `parenArg` (see its doc comment).
  | "List",    [a]    => some s!"List {parenArg a}"
  | "[]",      [a]    => some s!"List {parenArg a}"
  | "Maybe",   [a]    => some s!"Option {parenArg a}"
  | "Either",  [a, b] => some s!"Sum {parenArg a} {parenArg b}"
  -- Tuples. Lean's `×` is right-nested: `a × b × c = a × (b × c)`. Both the
  -- bare GHC tycon `(,)` (what the shim emits inside `tyConOpaque`) and any
  -- qualified form resolve here.
  | "(,)",   [a, b]    => some s!"({a} × {b})"
  | "GHC.Tuple.(,)", [a, b] => some s!"({a} × {b})"
  | "(,,)",  [a, b, c] => some s!"({a} × {b} × {c})"
  | "GHC.Tuple.(,,)", [a, b, c] => some s!"({a} × {b} × {c})"
  | "(,,,)", [a, b, c, d]           => some s!"({a} × {b} × {c} × {d})"
  | "GHC.Tuple.(,,,)", [a, b, c, d] => some s!"({a} × {b} × {c} × {d})"
  | "Ordering", []    => some "Ordering"
  | _,         _      => none

/-- GHC data constructor → Lean constructor reference. Both bare and
    module-qualified forms are accepted (Core delivers `GHC.Maybe.Just` etc.). -/
def dataConMap : String → Option String
  | "Just"    | "GHC.Maybe.Just"    => some "Option.some"
  | "Nothing" | "GHC.Maybe.Nothing" => some "Option.none"
  | ":"       => some "List.cons"
  | "[]"      => some "List.nil"
  | "True"    => some "Bool.true"
  | "False"   => some "Bool.false"
  | "()"      => some "Unit.unit"
  -- 2-tuple construction → `Prod.mk a b`. Both the bare pattern-position name
  -- `(,)` and the qualified value-position name `GHC.Tuple.(,)` resolve here.
  | "(,)"     | "GHC.Tuple.(,)" => some "Prod.mk"
  -- 3-/4-tuple construction. Eta-expanded lambdas, NOT `Prod.mk` (which is
  -- binary — left-applying it to 3 args is ill-typed): `(fun a b c => (a,b,c))`
  -- left-applies correctly at any saturation. 5+-tuples remain unmapped (loud).
  | "(,,)"  | "GHC.Tuple.(,,)"  => some "(fun a b c => (a, b, c))"
  | "(,,,)" | "GHC.Tuple.(,,,)" => some "(fun a b c d => (a, b, c, d))"
  -- Ordering constructors. Core delivers the qualified `GHC.Types.*` forms
  -- (confirmed via Generated/NumOrd.lean); bare forms kept as a hedge.
  | "LT" | "GHC.Types.LT" => some "Ordering.lt"
  | "EQ" | "GHC.Types.EQ" => some "Ordering.eq"
  | "GT" | "GHC.Types.GT" => some "Ordering.gt"
  | _         => none

/-- Transparent unwrapping data constructors: I#, W#, C# (and module-qualified variants).
    Boxing GHC's unboxed primitives. Treated as identity by Lower. -/
def isUnwrappingDataCon : String → Bool
  | "I#" | "GHC.Types.I#"
  | "W#" | "GHC.Types.W#"
  | "C#" | "GHC.Types.C#" => true
  | _                     => false

end GHCCore.Maps

