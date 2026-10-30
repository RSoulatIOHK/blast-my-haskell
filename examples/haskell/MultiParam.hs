{-# OPTIONS_GHC -fplugin GhcDump.Plugin #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE MultiParamTypeClasses #-}
-- | M3 Task 7 fixture: a MULTI-PARAMETER type class, end to end.
--
-- `class Convert a b` is the shape the three single-parameter seams named in the
-- plan meet: `ClassDecl.tyVars` (already a list since Task 1),
-- `stripClassConstraints` (a `C a b =>` constraint arrow), and the instance
-- attribution (`Emit.dfunMethodBinds` reads the dictionary POSITIONALLY, so it
-- never touches the space-joined head string that the single-parameter fallback
-- keys on). Both parameters are MONOMORPHIC data types: parameterized user data
-- types are unsupported (the decl plugin dumps no type parameters).
--
-- Deliberately in scope here:
--
--   * TWO methods, so the instance dictionary is the MULTI-FIELD shape
--     (`C:Convert @Celsius @Fahrenheit $cconv $cconvBack`) with TWO type
--     arguments to filter, not the single-method newtype shape.
--   * TWO instances of the same class, mirrored (`Convert Celsius Fahrenheit`
--     and `Convert Fahrenheit Celsius`), so all four `$c` binds collide by name
--     in pairs and the attribution has to disambiguate by UNIQUE.
--   * A CONSTRAINED polymorphic def (`convId :: Convert a b => a -> b`) plus a
--     monomorphic user of it — the only thing that exercises the new
--     `stripClassConstraints` arm (`[Convert a b]`) end to end. The wrappers
--     below bypass the header path entirely.
--   * A call site whose output type is pinned only by the ENCLOSING application
--     (`convThenValue`), because Lean has to re-derive by instance search what
--     GHC resolved by type inference.
--
-- Out of scope, and REFUSED rather than guessed (see the `M3 Task 7` block of
-- GhcCoreToLean/Tests/Unit.lean):
--
--   * Functional dependencies and overlapping instances. Both need a LANGUAGE
--     extension GHC will not accept implicitly, so a module using either is
--     rejected by GHC before any dump exists — the loudness is upstream of the
--     transpiler, not a check it makes.
--   * A SUPERCLASS on a multi-parameter class (`Sized a => Convert a b`, below).
--     The plugin's `supers` channel carries parent NAMES only, so with two
--     parameters there is nothing to apply the parent to but a guess;
--     `Emit.multiParamSupers` reports the drop and the emitted Lean class
--     carries no `extends`.
module MultiParam where
    import Prelude
    import Lean.Spec (lean)

    class Sized a where
        size :: a -> Int

    -- The superclass is here to be MEASURED, not used: `Sized a => Convert a b`
    -- emits as a plain `class Convert (a : Type) (b : Type)`, so a body that
    -- reached `size` through a `Convert a b` constraint would fail with `failed
    -- to synthesize Sized …`. That use site is deliberately absent — it is the
    -- limitation, and the warning (`Emit.multiParamSuperWarning`) is what makes
    -- it loud before `lake build` does. `size` at a monomorphic head still
    -- works, which is what `celsSize` pins.
    class Sized a => Convert a b where
        conv     :: a -> b
        convBack :: b -> a

    data Celsius    = Celsius Int
    data Fahrenheit = Fahrenheit Int

    -- Both heads need the superclass instance: the obligation is on the FIRST
    -- class parameter, and each of the two `Convert` instances puts a different
    -- type there.
    instance Sized Celsius where
        size (Celsius c) = c

    instance Sized Fahrenheit where
        size (Fahrenheit f) = f

    -- A deliberately cheap (and wrong-by-a-fraction) conversion: the point is
    -- the class machinery, and `*`/`+`/`-` keep the properties inside blaster's
    -- linear-integer fragment.
    instance Convert Celsius Fahrenheit where
        conv     (Celsius c)    = Fahrenheit (c * 2 + 32)
        convBack (Fahrenheit f) = Celsius (f - 32)

    -- The MIRRORED instance. Its `$cconv` has the same NAME as the one above and
    -- a different unique, and its `conv` has type `Fahrenheit -> Celsius`, so a
    -- first-value-argument match against a space-joined head
    -- (`"…Celsius" "…Fahrenheit"`) cannot tell the two apart — the dictionary
    -- attribution can.
    instance Convert Fahrenheit Celsius where
        conv     (Fahrenheit f) = Celsius (f - 32)
        convBack (Celsius c)    = Fahrenheit (c * 2 + 32)

    celsValue :: Celsius -> Int
    celsValue (Celsius c) = c

    fahrValue :: Fahrenheit -> Int
    fahrValue (Fahrenheit f) = f

    -- Monomorphic wrappers: the output type is pinned by the signature, which is
    -- what makes the Lean instance search decidable at the call site.
    cToF :: Celsius -> Fahrenheit
    cToF = conv

    fToC :: Fahrenheit -> Celsius
    fToC = conv

    -- `convBack` of the FIRST instance: `Fahrenheit -> Celsius`, i.e. the same
    -- type as `fToC` but a different method of a different instance. If the
    -- attribution paired the dictionary fields wrongly these two would swap
    -- bodies, so the properties below pin them separately.
    fToCBack :: Fahrenheit -> Celsius
    fToCBack = convBack

    -- Output type pinned only by the ENCLOSING application, never by a
    -- signature of its own.
    convThenValue :: Celsius -> Int
    convThenValue x = fahrValue (conv x)

    -- THE constrained-polymorphic shape: `Convert a b =>` must peel to
    -- `[Convert a b]`, or the first value binder gets the dictionary's type and
    -- the result type shifts.
    convId :: Convert a b => a -> b
    convId x = conv x

    useConvId :: Celsius -> Fahrenheit
    useConvId = convId

    -- The same constraint with the parameters in the OTHER order (`b -> a`), so
    -- the second class parameter is the one in leading position.
    --
    -- WHY there is no `roundTrip :: Convert a b => a -> a` here, calling both
    -- methods under one constraint: GHC REJECTS it. Without functional
    -- dependencies `b` is not determined by `a`, so `convBack (conv x)` leaves
    -- the intermediate type ambiguous — verbatim, `error: • Could not deduce
    -- (Convert a b0) arising from a type ambiguity check … The type variable
    -- ‘b0’ is ambiguous … To defer the ambiguity check to use sites, enable
    -- AllowAmbiguousTypes`. That is the fundep limitation being upstream of the
    -- transpiler: the shape never reaches a dump.
    convIdBack :: Convert a b => b -> a
    convIdBack y = convBack y

    useConvIdBack :: Fahrenheit -> Celsius
    useConvIdBack = convIdBack

    -- Both methods of the FIRST instance composed, monomorphically.
    cRoundTrip :: Celsius -> Celsius
    cRoundTrip x = fToCBack (cToF x)

    -- The dropped superclass's own method, reached at a monomorphic head (a
    -- `Sized Celsius` constraint GHC solves directly, not through `Convert`).
    celsSize :: Celsius -> Int
    celsSize = size

    [lean|
    theorem cToF_scales : ∀ (c : Int),
        fahrValue (cToF (Celsius.Celsius c)) = c * 2 + 32 := by blaster
    |]

    [lean|
    theorem fToC_offsets : ∀ (f : Int),
        celsValue (fToC (Fahrenheit.Fahrenheit f)) = f - 32 := by blaster
    |]

    -- `convBack` at the FIRST instance. Same input and output types as
    -- `fToC_offsets`, different method: the two bodies happen to agree here, so
    -- what this pins is that the field exists at all and elaborates.
    [lean|
    theorem fToCBack_offsets : ∀ (f : Int),
        celsValue (fToCBack (Fahrenheit.Fahrenheit f)) = f - 32 := by blaster
    |]

    -- The unpinned-at-the-call-site shape.
    [lean|
    theorem convThenValue_scales : ∀ (c : Int),
        convThenValue (Celsius.Celsius c) = c * 2 + 32 := by blaster
    |]

    -- The constrained-polymorphic def, instantiated monomorphically. This is the
    -- `[Convert a b]` header path: if the constraint arrow were not peeled,
    -- `useConvId` would not exist to be quantified over.
    [lean|
    theorem useConvId_scales : ∀ (c : Int),
        fahrValue (useConvId (Celsius.Celsius c)) = c * 2 + 32 := by blaster
    |]

    -- Same header path, parameters in the other order.
    [lean|
    theorem useConvIdBack_offsets : ∀ (f : Int),
        celsValue (useConvIdBack (Fahrenheit.Fahrenheit f)) = f - 32 := by blaster
    |]

    [lean|
    theorem cRoundTrip_composes : ∀ (c : Int),
        celsValue (cRoundTrip (Celsius.Celsius c)) = c * 2 + 32 - 32 := by blaster
    |]

    -- The superclass's method at a monomorphic head: unaffected by the drop.
    [lean|
    theorem celsSize_projects : ∀ (c : Int),
        celsSize (Celsius.Celsius c) = c := by blaster
    |]
