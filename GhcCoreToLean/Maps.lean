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
  | "$GhcCoreToLean.quotInt64" => some "Hs.quotInt64"
  | "$GhcCoreToLean.remInt64" => some "Hs.remInt64"
  | "$GhcCoreToLean.divInt64" => some "Hs.divInt64"
  | "$GhcCoreToLean.modInt64" => some "Hs.modInt64"
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
  -- String literals (M4 Task 2). Core spells `"hi" :: String` as
  -- `GHC.CString.unpackCString# "hi"#`, so the literal's Lean image is a Lean
  -- STRING literal (see `Emit.escapeStringLit`) and the unpacker's image is the
  -- `String → List Char` that turns it into the `[Char]` Haskell means.
  -- `String.toList` is LOAD-BEARING: a bare `"hi"` elaborates as `String`, which
  -- is not `List Char`, so dropping the conversion would be an ill-typed term
  -- wherever a Haskell `String` is used as a list.
  --
  -- BOTH unpackers are REQUIRED, not one plus a hedge. Measured on the pipeline's
  -- GHC 9.2.7: the plain variant appears only for a PURE-ASCII literal, and
  -- `unpackCStringUtf8#` for every non-ASCII one (`"caf\233"`, `"\255"`,
  -- `"\128169"`, and — before the shim repaired it — `"a\0b"`). Mapping only the
  -- plain one would fail loud on every accented string. Both take the same image:
  -- the byte-level difference between them is the shim's business, and by the time
  -- a payload reaches here it is already a decoded Lean `String` (or the module
  -- was refused — see `Emit.unrepresentableStringLiterals`).
  --
  -- OBSERVED NAMES ONLY, with the negatives recorded: `GHC.CString.unpackCString#`
  -- and `GHC.CString.unpackCStringUtf8#` are the two spellings in the dumps (the
  -- bare `unpackCString#` was NOT observed). `unpackAppendCString#` and
  -- `unpackFoldrCString#` — the RULE-introduced fusion forms — are 0-occurrence
  -- across every dump measured, exactly like `GHC.Base.augment` above, so they are
  -- deliberately absent rather than guessed at: a literal `++` still arrives as
  -- `List.append (String.toList "…")` at pass-0000.
  | "GHC.CString.unpackCString#"     => some "String.toList"
  | "GHC.CString.unpackCStringUtf8#" => some "String.toList"
  -- `Char` operations (M4 Task 4). ONLY TWO, and the smallness is the finding,
  -- not an omission — see the loud-fail block below for the seven `Data.Char`
  -- names that must stay unmapped and why.
  --
  -- OBSERVED NAMES, WITH THE NEGATIVES. The plan hedged `Data.Char.*` /
  -- `GHC.Char.*`; measured on the pipeline's GHC 9.2.7 over `CharOps.hs`, BOTH
  -- guesses are 0-occurrence and the real spellings are the DEFINING modules:
  -- `GHC.Base.ord` (×1) and `GHC.Unicode.isDigit` (×1), with
  -- `Data.Char.ord` ×0, `Data.Char.isDigit` ×0, `GHC.Char.ord` ×0,
  -- `GHC.Char.isDigit` ×0. `Data.Char` is a re-export module and Core names come
  -- from where a thing is DEFINED, so the `Data.Char.*` keys are not merely
  -- unobserved — they are the wrong shape and are deliberately absent rather than
  -- added "just in case", which would be a key that can never fire.
  -- No bare alphabetic keys either (`| "ord"`), per this map's standing rule:
  -- a user's own `ord` is a bare Core name and must keep resolving to their def.
  --
  -- `ord` IS SAFE, and the asymmetry is the whole reason. Every LEAN `Char` has a
  -- faithful Haskell image, so the surrogate gap enters only through
  -- CONSTRUCTION — i.e. through `chr`, which is why `ord` maps and `chr` cannot.
  -- Haskell `ord` returns `Int`, so the result is coerced like `length`/`gcd`.
  | "GHC.Base.ord" => some "(fun c => (c.toNat : Int))"
  | "$GhcCoreToLean.ordInt64" => some "(fun c => Int64.ofNat c.toNat)"
  -- `isDigit` is the ONE `Data.Char` predicate that AGREES on both sides: Haskell
  -- `GHC.Unicode.isDigit` and Lean v4.24 `Char.isDigit` both test ASCII 48..57
  -- only. Pinned in both languages by `CharOps.hs`, including the ARABIC-INDIC
  -- DIGIT FIVE `'٥'` (U+0665) — a Unicode digit that is `False` in Haskell and
  -- `false` in Lean, which is exactly the agreement being claimed.
  | "GHC.Unicode.isDigit" => some "Char.isDigit"
  | "GHC.Base.map"                => some "List.map"
  | "GHC.List.filter"             => some "List.filter"
  | "GHC.List.reverse"            => some "List.reverse"
  -- Int ranges (Enum dict is erased by Lower). `enumFrom`/`enumFromThen`
  -- (infinite) are intentionally NOT mapped — loud fail.
  | "GHC.Enum.enumFromTo"     => some "Hs.enumFromTo"
  | "$GhcCoreToLean.enumFromToInt64" => some "Hs.enumFromToInt64"
  | "GHC.Enum.enumFromThenTo" => some "Hs.enumFromThenTo"
  -- Int-indexed list ops. Haskell clamps negative counts to "empty/unchanged";
  -- `Int.toNat` clamps negatives to 0 — the semantics match exactly.
  | "GHC.List.take"      => some "(fun n xs => List.take n.toNat xs)"
  | "GHC.List.drop"      => some "(fun n xs => List.drop n.toNat xs)"
  | "$GhcCoreToLean.takeInt64" => some "(fun n xs => List.take n.toNatClampNeg xs)"
  | "$GhcCoreToLean.dropInt64" => some "(fun n xs => List.drop n.toNatClampNeg xs)"
  | "GHC.List.splitAt"   => some "Hs.splitAt"
  | "$GhcCoreToLean.splitAtInt64" => some "Hs.splitAtInt64"
  | "GHC.List.replicate" => some "(fun n x => List.replicate n.toNat x)"
  | "$GhcCoreToLean.replicateInt64" =>
      some "(fun n x => List.replicate n.toNatClampNeg x)"
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
  | "$GhcCoreToLean.lengthInt64" => some "(fun xs => Int64.ofNat (List.length xs))"
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
  -- Partial functions. Haskell `head`/`last`/`fromJust` are ⊥ ONLY on the
  -- empty list / `Nothing`; `!!` is ⊥ on ANY out-of-range index (a negative
  -- index reads position 0 after `Int.toNat` — still sound: ⊥ may be refined
  -- by any value). All are faithful on the rest of their domain, so they must
  -- NOT collapse to `default` everywhere (that breaks the defined domain,
  -- e.g. `head [1,2,3]`). We map to Lean's total `*D`/`getD` forms:
  -- faithful where Haskell is defined, and `default` (an arbitrary inhabitant)
  -- where Haskell is ⊥ — the documented partial-correctness tradeoff (see the
  -- README partial-functions bullet for the full per-function statement).
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
  -- maximum/minimum: ⊥ only on []. Same getD-default partial-correctness
  -- route as head/last (registered in Emit.isPartialDefaultName so
  -- polymorphic defs get an [Inhabited t] binder). Foldable-qualified
  -- names observed (like sum/elem); GHC.List.* hedged.
  | "Data.Foldable.maximum" | "GHC.List.maximum" => some "(fun xs => (List.max? xs).getD default)"
  | "Data.Foldable.minimum" | "GHC.List.minimum" => some "(fun xs => (List.min? xs).getD default)"
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
  | "$GhcCoreToLean.fromIntegerInt64" => some "Int64.ofInt"
  | "$GhcCoreToLean.toIntegerInt64" => some "Int64.toInt"
  | "$GhcCoreToLean.int64ToInteger" => some "Int64.toInt"
  | "$GhcCoreToLean.integerToInt64" => some "Int64.ofInt"
  | "GHC.Num.signum"        => some "(fun a => if a < 0 then -1 else if a > 0 then 1 else 0)"
  -- divMod floors (fdiv/fmod); quotRem truncates (tdiv/tmod). Returns a pair.
  | "GHC.Real.divMod"       => some "(fun a b => (Int.fdiv a b, Int.fmod a b))"
  | "GHC.Real.quotRem"      => some "(fun a b => (Int.tdiv a b, Int.tmod a b))"
  | "$GhcCoreToLean.divModInt64" => some "Hs.divModInt64"
  | "$GhcCoreToLean.quotRemInt64" => some "Hs.quotRemInt64"
  -- Lean `Int.gcd`/`Int.lcm` return `Nat`; Haskell returns the numeric type.
  | "GHC.Real.gcd"          => some "(fun a b => (Int.gcd a b : Int))"
  | "GHC.Real.lcm"          => some "(fun a b => (Int.lcm a b : Int))"
  | "$GhcCoreToLean.gcdInt64" => some "Hs.gcdInt64"
  | "$GhcCoreToLean.lcmInt64" => some "Hs.lcmInt64"
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
  -- Internal marker introduced by `Lower.machineInts` in conservative mode.
  -- It cannot collide with a Haskell source name because `$` is not legal in
  -- an ordinary Haskell type constructor.
  | "$GhcCoreToLean.Int64", [] => some "Int64"
  | "Integer", []     => some "Int"
  | "Word",    []     => some "Nat"
  | "Word#",   []     => some "Nat"
  | "GHC.Prim.Word#", [] => some "Nat"
  | "Bool",    []     => some "Bool"
  | "Char",    []     => some "Char"
  -- Core keeps the SYNONYM in binder types (`{"tag":"TyCon","name":"String"}`),
  -- so a `String`-typed def needs this arm as well as the `[] [Char]` one below:
  -- without it a `String` binder emitted `(GHCCore.tyConOpaque "String")` while
  -- its BODY emitted a `List Char`. Only the bare spelling is observed; a
  -- qualified `GHC.Base.String` was NOT seen in any dump and is not guessed at.
  -- Same exposure as the `Int`/`Bool` arms: a user type of that name would be
  -- hijacked here, which is why the roadmap's builtin-name arms stay a fixed,
  -- observed list.
  | "String",  []     => some "List Char"
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
  -- GHC 9.2.7 retains the qualified constructor in value position for
  -- source-written `(:)` in data-ordlist's recursive list functions.
  | ":" | "GHC.Types.:" => some "List.cons"
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

/-- Haskell BUILTIN class → the Lean instance-implicit binder templates that a
    signature constraint on that class becomes (`Eq a => …` ⇒ `[BEq t]`). The
    literal `{t}` in each template is substituted with the constrained type
    variable's emitted name by `Emit.stripClassConstraints`.

    Only BUILTIN classes belong here. A USER class `C` keeps emitting `[C t]` —
    its Lean image is the `class C` the transpiler emits — and is matched first,
    so this map cannot hijack it.

    An unmapped builtin (`Fractional`, `Integral`, `Real`, `Show`, `Enum`, …) is
    deliberately ABSENT rather than approximated: its constraint arrow then stays
    in the signature, the def's first value binder is typed as the (already
    value-erased) dictionary, and the generated file fails to elaborate. That is
    LOUD — the project's fail mode of choice — and it is the signal that a new
    entry is wanted here.

    ORDER INSIDE EACH LIST IS LOAD-BEARING, not cosmetic. `DecidableLT t` is
    `DecidableRel (LT.lt : t → t → Prop)` (`Init/Prelude.lean:1250`), so it only
    elaborates once `LT t` is already bound; likewise `DecidableLE`/`LE`.
    `Tests/Unit.lean` pins the whole sequence, not just membership, so a reorder
    cannot pass silently.

    Why `Ord` needs EIGHT binders rather than `[Ord t]`: the transpiler's images
    of the Haskell `Ord` methods are `decide (a < b)` / `decide (a ≤ b)` (Lean's
    `<`/`≤` are `Prop`-valued), `Min.min` / `Max.max`, and `compare` — and Lean
    core deliberately leaves `ltOfOrd`/`leOfOrd`/`minOfLe`/`maxOfLe` as plain
    defs, NOT instances. `[BEq t]` is in the set because Haskell's `Ord a`
    implies `Eq a` (`$p1Ord`), so an `Ord`-constrained body may legitimately use
    `==`. Measured: `[Ord t]` alone fails on `LT`/`LE`/`Min`; adding
    `[LT t] [LE t] [Min t] [Max t] [BEq t]` still fails on `Decidable (a < b)`.
    See the `M3 Task 3` block in `Tests/Unit.lean` for the probe transcript and
    for why the coherence-preserving alternative (`[Ord t]` only, deriving
    LT/LE/Min/Max inside the body) was rejected.

    Why `Num` is only FOUR: numeric literals emit Int-ascribed (`emitLiteral`
    gives `(1 : Int)`), so `OfNat t n` binders would be dead weight — a literal
    in a `Num a`-polymorphic body is a hard type error (loud) either way. `abs`
    and `signum` likewise stay loud there: their images test `a < 0`, which needs
    the `Ord` binder set that a `Num a` constraint does not supply. -/
def classConMap : String → Option (List String)
  -- Bare names are what the shim delivers for constraint heads (observed in
  -- /tmp/transpile-BuiltinConstraints.json: `{"name": "Eq", "tag": "TyCon"}`);
  -- the qualified forms are a forward hedge, as in `dataConMap`.
  | "Eq"  | "GHC.Classes.Eq"  => some ["[BEq {t}]"]
  | "Ord" | "GHC.Classes.Ord" =>
    some ["[Ord {t}]", "[LT {t}]", "[LE {t}]", "[DecidableLT {t}]", "[DecidableLE {t}]",
          "[Min {t}]", "[Max {t}]", "[BEq {t}]"]
  | "Num" | "GHC.Num.Num" => some ["[Add {t}]", "[Sub {t}]", "[Mul {t}]", "[Neg {t}]"]
  | _ => none

/-- Transparent unwrapping data constructors: I#, W#, C# (and module-qualified variants).
    Boxing GHC's unboxed primitives. Treated as identity by Lower. -/
def isUnwrappingDataCon : String → Bool
  | "I#" | "GHC.Types.I#"
  | "W#" | "GHC.Types.W#"
  | "C#" | "GHC.Types.C#" => true
  | _                     => false

end GHCCore.Maps
