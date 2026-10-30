-- A source-exact slice of data-ordlist 0.4.7.0, Data.List.Ordered.
-- Copyright (c) 2009-2011 Leon P Smith. See LICENSE in this directory.
-- The three *By definitions below are copied verbatim. The Int wrappers
-- after them are local test entry points, not upstream library definitions.
module OrderedPilot where

isSortedBy :: (a -> a -> Bool) -> [a] -> Bool
isSortedBy lte = loop
  where
    loop []       = True
    loop [_]      = True
    loop (x:y:zs) = (x `lte` y) && loop (y:zs)

memberBy :: (a -> a -> Ordering) -> a -> [a] -> Bool
memberBy cmp x = loop
  where
    loop []     = False
    loop (y:ys) = case cmp x y of
                    LT -> False
                    EQ -> True
                    GT -> loop ys

insertSetBy :: (a -> a -> Ordering) -> a -> [a] -> [a]
insertSetBy cmp = loop
  where
    loop x [] = [x]
    loop x (y:ys) = case cmp x y of
            LT -> x:y:ys
            EQ -> x:ys
            GT -> y:loop x ys

isSortedInt :: [Int] -> Bool
isSortedInt = isSortedBy (<=)

memberInt :: Int -> [Int] -> Bool
memberInt = memberBy compare

insertSetInt :: Int -> [Int] -> [Int]
insertSetInt = insertSetBy compare

{- @lean
theorem insert_empty (x : Int64) : insertSetInt x [] = [x] := by rfl
theorem member_empty (x : Int64) : memberInt x [] = false := by rfl
theorem sorted_empty : isSortedInt [] = true := by rfl

-- Blaster handles the generic list induction cases. The bridge to the GHC Int
-- wrapper stays in Lean because this Blaster revision cannot encode Int64.
theorem insert_member_generic {α : Type} (cmp : α → α → Ordering)
    (x : α) (xs : List α) (hself : cmp x x = Ordering.eq) :
    memberBy cmp x (insertSetBy cmp x xs) = true := by
  induction xs with
  | nil => blaster (timeout: 5)
  | cons y ys ih =>
      cases h : cmp x y with
      | lt => blaster (timeout: 5)
      | eq => blaster (timeout: 5)
      | gt => blaster (timeout: 5)

theorem member_insert (x : Int64) (xs : List Int64) :
    memberInt x (insertSetInt x xs) = true := by
  simpa [memberInt, insertSetInt] using
    insert_member_generic compare x xs (by simp [compare, compareOfLessAndEq])

theorem mem_insert (x v : Int64) (xs : List Int64) :
    v ∈ insertSetBy.loop_2965 compare x xs → v = x ∨ v ∈ xs := by
  induction xs with
  | nil => simp [insertSetBy.loop_2965]
  | cons y ys ih =>
      cases h : compare x y with
      | lt => simp_all [insertSetBy.loop_2965]
      | eq => simp_all [insertSetBy.loop_2965]
      | gt =>
          simp only [insertSetBy.loop_2965, h, List.mem_cons]
          intro hv
          rcases hv with rfl | hv
          · exact Or.inr (Or.inl rfl)
          · rcases ih hv with rfl | hv'
            · exact Or.inl rfl
            · exact Or.inr (Or.inr hv')

theorem pairwise_insert (x : Int64) (xs : List Int64) :
    xs.Pairwise (· ≤ ·) →
    (insertSetBy.loop_2965 compare x xs).Pairwise (· ≤ ·) := by
  induction xs with
  | nil => intro _; simp [insertSetBy.loop_2965]
  | cons y ys ih =>
      intro hs
      have ⟨hy, hys⟩ := List.pairwise_cons.mp hs
      cases h : compare x y with
      | lt =>
          have hxy : x ≤ y := Int64.le_of_lt (compareOfLessAndEq_eq_lt.mp h)
          have hall : ∀ a, a ∈ y :: ys → x ≤ a := by
            intro a ha
            rcases List.mem_cons.mp ha with rfl | ha'
            · exact hxy
            · exact Int64.le_trans hxy (hy a ha')
          simpa [insertSetBy.loop_2965, h] using
            (List.pairwise_cons.mpr ⟨hall, hs⟩)
      | eq =>
          have hxy : x = y :=
            (compareOfLessAndEq_eq_eq Int64.le_refl Int64.not_le).mp h
          subst x
          simpa [insertSetBy.loop_2965, h] using hs
      | gt =>
          have hyx : y ≤ x := Int64.le_of_lt
            ((compareOfLessAndEq_eq_gt Int64.le_antisymm Int64.le_total Int64.not_le x y).mp h)
          have hall : ∀ a, a ∈ insertSetBy.loop_2965 compare x ys → y ≤ a := by
            intro a ha
            rcases mem_insert x a ys ha with rfl | ha'
            · exact hyx
            · exact hy a ha'
          simpa [insertSetBy.loop_2965, h] using
            (List.pairwise_cons.mpr ⟨hall, ih hys⟩)

theorem pairwise_to_sorted_loop (xs : List Int64) :
    xs.Pairwise (· ≤ ·) →
    isSortedBy.loop_3039 (fun a b => decide (a ≤ b)) xs = true := by
  induction xs with
  | nil => intro _; rfl
  | cons x xs ih =>
      cases xs with
      | nil => intro _; rfl
      | cons y ys =>
          intro hs
          have hxy : x ≤ y := (List.pairwise_cons.mp hs).1 y (by simp)
          have htail := (List.pairwise_cons.mp hs).2
          simpa [isSortedBy.loop_3039, hxy] using ih htail

theorem sorted_loop_to_pairwise (xs : List Int64) :
    isSortedBy.loop_3039 (fun a b => decide (a ≤ b)) xs = true →
    xs.Pairwise (· ≤ ·) := by
  induction xs with
  | nil => intro _; simp
  | cons x xs ih =>
      cases xs with
      | nil => intro _; simp
      | cons y ys =>
          intro hs
          have hsplit : (decide (x ≤ y) &&
              isSortedBy.loop_3039 (fun a b => decide (a ≤ b)) (y :: ys)) = true := by
            simpa [isSortedBy.loop_3039] using hs
          have hxy : x ≤ y := of_decide_eq_true (Bool.and_eq_true_iff.mp hsplit).1
          have htail := ih (Bool.and_eq_true_iff.mp hsplit).2
          apply List.pairwise_cons.mpr
          constructor
          · intro a ha
            rcases List.mem_cons.mp ha with rfl | ha'
            · exact hxy
            · exact Int64.le_trans hxy ((List.pairwise_cons.mp htail).1 a ha')
          · exact htail

theorem sorted_insert (x : Int64) (xs : List Int64) :
    isSortedInt xs = true → isSortedInt (insertSetInt x xs) = true := by
  intro h
  change isSortedBy.loop_3039 (fun a b => decide (a ≤ b)) xs = true at h
  change isSortedBy.loop_3039 (fun a b => decide (a ≤ b))
      (insertSetBy.loop_2965 compare x xs) = true
  exact pairwise_to_sorted_loop _
    (pairwise_insert x xs (sorted_loop_to_pairwise xs h))

theorem insert_idempotent_generic {α : Type} (cmp : α → α → Ordering)
    (x : α) (xs : List α) (hself : cmp x x = Ordering.eq) :
    insertSetBy cmp x (insertSetBy cmp x xs) = insertSetBy cmp x xs := by
  induction xs with
  | nil => blaster (timeout: 5)
  | cons y ys ih =>
      cases h : cmp x y with
      | lt => blaster (timeout: 5)
      | eq => blaster (timeout: 5)
      | gt => blaster (timeout: 5)

theorem insert_idempotent (x : Int64) (xs : List Int64) :
    insertSetInt x (insertSetInt x xs) = insertSetInt x xs := by
  simpa [insertSetInt] using
    insert_idempotent_generic compare x xs (by simp [compare, compareOfLessAndEq])
-}
