module ImplicitTypo where
value :: Bool
value = True
{- @lean
-- Without autoImplicit=false, Lean silently quantifies over this typo.
theorem mistaken : misspelled = misspelled := by rfl
-}
