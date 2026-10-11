import Mathlib.Order.Basic -- Importing here type class `LinearOrder`

/-! Insertion sort -/
namespace InsertionSort -- To avoid captures from Mathlib

/-- Permutations on lists

  We define permutations on lists are a composition of transpositions,
  that is, exchanges of two adjacent keys. The inductive proposition
  `Perm s t` means that `s` is a permutation of `t`.
-/
inductive Perm {α : Type} : List α -> List α → Prop where
| empty                            : Perm [] []
| transpose (x y : α) (s : List α) : Perm (x::y::s) (y::x::s)
| push (x : α) (s t : List α)      : Perm s t -> Perm (x::s) (x::t)
| trans (s t u : List α)           : Perm s t -> Perm t u -> Perm s u

lemma Perm.symmetry {α : Type} (s t : List α) : Perm s t -> Perm t s :=
by intro h
   induction h with
   | empty                     => exact Perm.empty
   | transpose x y s           => exact Perm.transpose y x s
   | push x s t _ ih           => exact Perm.push x t s ih
   | trans s t u h1 h2 ih1 ih2 => exact Perm.trans u t s ih2 ih1

lemma Perm.reflexivity {α : Type} (s : List α) : Perm s s :=
by induction s with
   | nil         => exact Perm.empty
   | cons x s ih => exact Perm.push x s s ih

/-- Insertion in non-decreasing order -/
def insert {α : Type} [LinearOrder α] (x : α) : List α → List α
| []     => [x]
| y :: s => if x ≤ y then x :: y :: s else y :: insert x s

theorem insert.nil {α : Type} [LinearOrder α] (x : α) : insert x [] = [x] := rfl

theorem insert.cons {α : Type} [LinearOrder α] (x y : α) (s : List α)
  : insert x (y :: s) = if x ≤ y then x :: y :: s else y :: insert x s := rfl

attribute [irreducible] insert

lemma Insert.extends {α : Type} [LinearOrder α] (x : α) (s : List α) :
  Perm (insert x s) (x :: s) :=
by induction s with
   | nil =>
      -- ⊢ Perm (insert x []) [x]
      conv => enter [1]; exact insert.nil x
      -- ⊢ Perm [x] [x]
      exact Perm.reflexivity [x]
--    -- Alternative for the whole case:
--    -- ⊢ Perm (insert x []) [x]
--    -- insert.nil x : insert x [] = [x]
--    -- Perm.reflexivity [x] : Perm [x] [x]
--    -- insert.nil x ▸ Perm.reflexivity [x] : Perm (insert x []) [x]
--    exact insert.nil x ▸ Perm.reflexivity [x]
   | cons y s ih =>
       -- ih : Perm (insert x s) (x :: s)
       by_cases hxy : x ≤ y
       · -- ite_eq_left hxy : (if x ≤ y then x :: y :: s else y :: insert x s) = x :: y :: s
         -- ⊢ Perm (insert x (y :: s)) (x :: y :: s)
         conv =>
           enter [1] -- | insert x (y :: s)
           exact Eq.trans (insert.cons x y s) (ite_eq_left hxy)
         -- ⊢ Perm (x :: y :: s) (x :: y :: s)
         exact Perm.reflexivity (x :: y :: s)
       · -- hxy : ¬ x ≤ y
         -- ite_eq_right hxy : (if x ≤ y then x :: y :: s else y :: insert x s) = y :: insert x s
         conv =>
           enter [1] -- | insert x (y :: s)
           exact Eq.trans (insert.cons x y s) (ite_eq_right hxy)
         -- ⊢ Perm (y :: insert x s) (x :: y :: s)
         have h : Perm (y :: insert x s) (y :: x :: s) :=
           Perm.push y (insert x s) (x :: s) ih
         have h' : Perm (y :: x :: s) (x :: y :: s) :=
           Perm.symmetry _ _ (Perm.transpose x y s)
         exact Perm.trans _ _ _ h h'

/-- Inductive predicate for sorted lists -/
inductive Ordered {α : Type} (r : α → α → Prop) : List α → Prop where
| nil                         : Ordered r []
| singleton (x : α)           : Ordered r [x]
| cons (x y : α) (s : List α) : r x y → Ordered r (y :: s) → Ordered r (x :: y :: s)

def Sorted {α : Type} [LinearOrder α] : List α → Prop := Ordered (· ≤ ·)

example {α : Type} [LinearOrder α] (x : α) : Sorted [x] := by
  -- `Sorted [x]` is implicitly unfolded into `Ordered (· ≤ ·) [x]`
  -- (because it is not an inductive definition)
  -- which is unified with `Ordered ?r [x]`, which matches iff `?r := (· ≤ ·)`.
  exact Ordered.singleton x

lemma Insert.preserves_order {α : Type} [LinearOrder α] (x : α) (s : List α) :
  Sorted s → Sorted (insert x s) :=
by induction s with
   | nil =>
       -- ⊢ Sorted [] → Sorted (insert x [])
       intro _
       -- ⊢ Sorted (insert x [])
       conv => enter [1]; exact insert.nil x
       -- ⊢ Sorted [x]
       exact Ordered.singleton x
--     -- Alternative for the whole case:
--     -- insert.nil x : insert x [] = [x]
--     -- Ordered.singleton x : Ordered (· ≤ ·) [x] = Sorted [x]
--     -- insert.nil x ▸ Ordered.singleton x : Sorted (insert x [])
--     exact fun _ => insert.nil x ▸ Ordered.singleton x
   | cons y s ih =>
       -- ih : Sorted s → Sorted (insert x s)
       -- ⊢ Sorted (y :: s) → Sorted (insert x (y :: s))
       intro hs
       -- hs : Sorted (y :: s)
       by_cases hxy : x ≤ y
       · -- ite_eq_left hxy : (if x ≤ y then x :: y :: s else y :: insert x s) = x :: y :: s
         -- ⊢ Sorted (insert x (y :: s))
         conv =>
           enter [1] -- | insert x (y :: s)
           exact Eq.trans (insert.cons x y s) (ite_eq_left hxy)
         -- ⊢ Sorted (x :: y :: s)
         exact Ordered.cons x y s hxy hs
--       --- Alternative
--       have then_branch : insert x (y :: s) = x :: y :: s :=
--         Eq.trans (insert.cons x y s) (ite_eq_left hxy)
--       exact then_branch ▸ Ordered.cons x y s hxy hs
       · -- hxy : ¬ x ≤ y
         conv => enter [1]; exact Eq.trans (insert.cons x y s) (ite_eq_right hxy)
         -- ⊢ Sorted (y :: insert x s)
         have hyx : y ≤ x := le_of_not_ge hxy
         cases s with
         | nil =>
             -- ⊢ Sorted (y :: insert x [])
             conv => enter [1,2]; exact insert.nil x
             -- ⊢ Sorted (y :: [x])
             exact Ordered.cons y x [] hyx (Ordered.singleton x)
         | cons z t =>
             cases hs with
             | cons _ _ _ hyz hzt =>
                 -- hyz : y ≤ z
                 -- hzt : Sorted (z :: t)
                 by_cases hxz : x ≤ z
                 · conv =>
                     enter [1,2] -- | insert x (z :: t)
                     exact Eq.trans (insert.cons x z t) (ite_eq_left hxz)
                   -- ⊢ Sorted (y :: x :: z :: t)
                   exact Ordered.cons y x (z :: t) hyx (Ordered.cons x z t hxz hzt)
                 · conv =>
                     enter [1,2] -- | insert x (z :: t)
                     exact Eq.trans (insert.cons x z t) (ite_eq_right hxz)
                   -- ⊢ Sorted (y :: z :: insert x t)
                   have h : Sorted (insert x (z :: t)) := ih hzt
                   conv at h =>
                     enter [1] -- | insert x (z :: t)
                     exact Eq.trans (insert.cons x z t) (ite_eq_right hxz)
                   -- h : Sorted (z :: insert x t)
                   -- ⊢ Sorted (y :: z :: insert x t)
                   exact Ordered.cons y z (insert x t) hyz h

/-- Sorting -/
def sort {α : Type} [LinearOrder α] : List α → List α
| []     => []
| x :: s => insert x (sort s)

theorem sort.nil {α : Type} [LinearOrder α] :
  sort (α := α) ([] : List α) = [] := rfl

theorem sort.cons {α : Type} [LinearOrder α] (x : α) (s : List α) :
  sort (x :: s) = insert x (sort s) := rfl

attribute [irreducible] sort

theorem Sort.soundness {α : Type} [LinearOrder α] (s : List α) :
  Sorted (sort s) ∧ Perm (sort s) s :=
by induction s with
   | nil =>
       -- ⊢ Sorted (sort []) ∧ Perm (sort []) []
       constructor
       · -- ⊢ Sorted (sort [])
         conv => enter [1]; exact sort.nil
         -- ⊢ Sorted []
         exact Ordered.nil
       · -- ⊢ Perm (sort []) []
         conv => enter [1]; exact sort.nil
         -- ⊢ Perm [] []
         exact Perm.empty
   | cons x s ih =>
       -- ih : Sorted (sort s) ∧ Perm (sort s) s
       -- ⊢ Sorted (sort (x :: s)) ∧ Perm (sort (x :: s)) (x :: s)
       constructor
       · -- ⊢ Sorted (sort (x :: s))
         conv => enter [1]; exact sort.cons x s
         -- ⊢ Sorted (insert x (sort s))
         exact Insert.preserves_order x (sort s) ih.1
       · -- ⊢ Perm (sort (x :: s)) (x :: s)
         conv => enter [1]; exact sort.cons x s
         -- ⊢ Perm (insert x (sort s)) (x :: s)
         have h : Perm (insert x (sort s)) (x :: sort s) :=
           Insert.extends x (sort s)
         have h' : Perm (x :: sort s) (x :: s) :=
           Perm.push x (sort s) s ih.2
         exact Perm.trans _ _ _ h h'

end InsertionSort
