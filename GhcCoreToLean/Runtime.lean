/-! # Haskell runtime support helpers

Named Lean images for `base` functions whose faithful translation is too
complex for a readable inline lambda in `Maps.lean` (spec: 2026-07-24
coverage-roadmap §"runtime support module"). Generated files import this
module unconditionally; helpers are ordinary defs, `#guard`-tested in
`Tests/Unit.lean`, and stable named symbols for Blaster to unfold. -/

namespace Hs

end Hs
