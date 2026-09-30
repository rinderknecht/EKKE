import Mathlib.Order.Basic -- Importing here type class `LinearOrder`

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

lemma Insert.extends {α : Type} [LinearOrder α] (x : α) (s : List α) :
  Perm (insert x s) (x :: s) :=
by induction s with
   | nil =>
       -- ⊢ Perm (insert x []) [x]
       -- Implicit unfolding of `insert|1` by `exact`:
       -- ⊢ Perm [x] [x]
       exact Perm.reflexivity [x]
   | cons y s ih =>
       by_cases hxy : x ≤ y
       · rw [insert, ite_eq_left hxy] -- or: `simp [insert, hxy]`
         -- ⊢ Perm (x :: y :: s) (x :: y :: s)
         exact Perm.reflexivity (x :: y :: s)
       · -- hxy : ¬ x ≤ y
         rw [insert, ite_eq_right hxy] -- or: `simp [insert, hxy]`
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

lemma Insert.preserves_order {α : Type} [LinearOrder α] (x : α) (s : List α) :
  Sorted s → Sorted (insert x s) :=
by induction s with
   | nil =>
       -- ⊢ Sorted [] → Sorted (insert x [])
       -- `Sorted []` dropped by `_`; implicit unfolding of `insert|1` by `exact`:
       -- ⊢ Sorted [] → Sorted [x]
       exact fun _ => Ordered.singleton x
   | cons y s ih =>
       -- ih : Sorted s → Sorted (insert x s)
       -- ⊢ Sorted (y :: s) → Sorted (insert x (y :: s))
       intro hs
       -- hs : Sorted (y :: s)
       by_cases hxy : x ≤ y
       · rw [insert, ite_eq_left hxy] -- or: `simp [insert, hxy]`
         -- ⊢ Sorted (if x ≤ y then x :: y :: s else y :: insert x s)
         -- ⊢ Sorted (x :: y :: s)
         exact Ordered.cons x y s hxy hs
       · -- hxy : ¬ x ≤ y
         rw [insert, ite_eq_right hxy] -- or: `simp [insert, hxy]`
          -- ⊢ Sorted (if x ≤ y then x :: y :: s else y :: insert x s)
         -- ⊢ Sorted (y :: insert x s)
         have hyx : y ≤ x := le_of_not_ge hxy
         cases s with
         | nil =>
             -- ⊢ Sorted (y :: insert x [])
             -- Implicit unfolding of `insert|1` by `exact`:
             -- ⊢ Sorted (y :: [x])
             exact Ordered.cons y x [] hyx (Ordered.singleton x)
         | cons z t =>
             cases hs with
             | cons _ _ _ hyz hzt =>
                 -- hyz : y ≤ z
                 -- hzt : Sorted (z :: t)
                 by_cases hxz : x ≤ z
                 · rw [insert, ite_eq_left hxz] -- or: `simp [insert, hxz]`
                   -- ⊢ Sorted (y :: if x ≤ z then x :: z :: t else z :: insert x t)
                   -- ⊢ Sorted (y :: x :: z :: t)
                   exact Ordered.cons y x (z :: t) hyx (Ordered.cons x z t hxz hzt)
                 · rw [insert, ite_eq_right hxz]
                   -- ⊢ Sorted (y :: if x ≤ z then x :: z :: t else z :: insert x t)
                   -- ⊢ Sorted (y :: insert x (z :: t))
                   have h : Sorted (insert x (z :: t)) := ih hzt
                   rw [insert, ite_eq_right hxz] at h -- or: `simp [insert, hxz] at h`
                   -- h : Sorted (if x ≤ z then x :: z :: t else z :: insert x t)
                   -- h : Sorted (z :: insert x t)
                   exact Ordered.cons y z (insert x t) hyz h

/-- Sorting -/
def sort {α : Type} [LinearOrder α] : List α → List α
| []     => []
| x :: s => insert x (sort s)

theorem Sort.soundness {α : Type} [LinearOrder α] (s : List α) :
  Sorted (sort s) ∧ Perm (sort s) s :=
by induction s with
   | nil =>
       -- ⊢ Sorted (sort []) ∧ Perm (sort []) []
       -- constructor
       -- · -- ⊢ Sorted (sort [])
       --   -- Implicit unfolding of `sort|1` by `exact`:
       --   -- ⊢ Sorted []
       --   exact Ordered.nil
       -- · -- ⊢ Perm (sort []) []
       --   -- Implicit unfolding of `sort|1` by `exact`:
       --   -- ⊢ Perm [] []
       --   exact Perm.empty
       exact ⟨Ordered.nil, Perm.empty⟩
   | cons x s ih =>
       -- ih : Sorted (sort s) ∧ Perm (sort s) s
       constructor
       · -- ⊢ Sorted (sort (x :: s))
         -- Implicit unfolding of `sort|2` by `exact`:
         -- ⊢ Sorted (insert x (sort s))
         exact Insert.preserves_order x (sort s) ih.1
       · -- ⊢ Perm (sort (x :: s)) (x :: s)
         have h : Perm (insert x (sort s)) (x :: sort s) :=
           Insert.extends x (sort s)
         have h' : Perm (x :: sort s) (x :: s) :=
           Perm.push x (sort s) s ih.2
         -- Implicit unfolding of `sort|2` by `exact`:
         -- ⊢ Perm (insert x (sort s)) (x :: s)
         exact Perm.trans _ _ _ h h'

end InsertionSort
