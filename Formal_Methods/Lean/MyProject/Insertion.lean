import Mathlib.Order.Basic -- Importing here type class `LinearOrder`

namespace InsertionSort -- To avoid captures from Mathlib

-- Insertion sort

def insert {α : Type} [LinearOrder α] (x : α) : List α → List α
| []     => [x]
| y :: s => if x ≤ y then x :: y :: s else y :: insert x s

def ins_sort {α : Type} [LinearOrder α] : List α → List α
| []     => []
| x :: s => insert x (ins_sort s)

/-- Transpositions on lists

  We define permutations on lists are a composition of transpositions,
  that is, the exchange of two adjacent keys. The inductive
  proposition `Perm s t` means that `s` and `t` are a permutation of
  each other.
-/
inductive Perm {α : Type} : List α -> List α → Prop where
| nil                           : Perm [] []
| transp (x y : α) (s : List α) : Perm (x::y::s) (y::x::s)
| push (x : α) (s t : List α)   : Perm s t -> Perm (x::s) (x::t)
| trans (s t u : List α)        : Perm s t -> Perm t u -> Perm s u

/-- Symmetry of permutations -/
lemma symm_perm {α : Type} (s t : List α) : Perm s t -> Perm t s :=
  by intro h
     induction h with
     | nil                       => exact Perm.nil
     | transp x y s              => exact Perm.transp y x s
     | push x s t _ ih           => exact Perm.push x t s ih
     | trans s t u h1 h2 ih1 ih2 => exact Perm.trans u t s ih2 ih1

/-- We actually need to prove that `Perm` is reflexive -/
lemma refl_perm {α : Type} (s : List α) : Perm s s :=
  by induction s with
  | nil         => exact Perm.nil
  | cons x s ih => exact Perm.push x s s ih

/-- Insertion adds a key somewhere -/
lemma ins_cmp {α : Type} [LinearOrder α] (x : α) (s : List α) : Perm (insert x s) (x::s) :=
  by induction s with
  | nil =>
      -- ⊢ Perm (insert x []) [x]
      unfold insert
      -- ⊢ Perm [x] [x]
      exact refl_perm [x]
  | cons y s ih =>
      by_cases hxy : x ≤ y
      · rw [insert, ite_eq_left hxy] -- or: `simp [insert, hxy]`
        -- ⊢ Perm (x :: y :: s) (x :: y :: s)
        exact refl_perm (x :: y :: s)
      · -- hxy : ¬ x ≤ y
        rw [insert, ite_eq_right hxy] -- or: `simp [insert, hxy]`
        -- ⊢ Perm (y :: insert x s) (x :: y :: s)
        have h : Perm (y :: insert x s) (y :: x :: s) :=
          Perm.push y (insert x s) (x :: s) ih
        have h' : Perm (y :: x :: s) (x :: y :: s) :=
          symm_perm _ _ (Perm.transp x y s)
        exact Perm.trans _ _ _ h h'

/-- Inductive predicate for sorted lists -/
inductive Sorted {α : Type} (r : α → α → Prop) : List α → Prop where
| nil                         : Sorted r []
| singleton (x : α)           : Sorted r [x]
| cons (x y : α) (s : List α) : r x y → Sorted r (y :: s) → Sorted r (x :: y :: s)

/-- Insertion preserves ordering -/
lemma ins_ord {α : Type} [LinearOrder α] (x : α) (s : List α) :
  Sorted (· ≤ ·) s → Sorted (· ≤ ·) (insert x s) :=
  by induction s with
  | nil =>
      -- ⊢ Sorted (· ≤ ·) [] → Sorted (· ≤ ·) (insert x [])
      -- `Sorted (· ≤ ·) []` dropped by `_`; modulo definition of `insert|1`:
      -- ⊢ Sorted (· ≤ ·) [] → Sorted (· ≤ ·) [x]
      exact fun _ => Sorted.singleton x
  | cons y s ih =>
      -- ih : Sorted (· ≤ ·) s → Sorted (· ≤ ·) (insert x s)
      -- ⊢ Sorted (· ≤ ·) (y :: s) → Sorted (· ≤ ·) (insert x (y :: s))
      intro hs
      -- hs : Sorted (· ≤ ·) (y :: s)
      by_cases hxy : x ≤ y
      · rw [insert, ite_eq_left hxy] -- or: `simp [insert, hxy]`
        -- ⊢ Sorted (· ≤ ·) (if x ≤ y then x :: y :: s else y :: insert x s)
        -- ⊢ Sorted (· ≤ ·) (x :: y :: s)
        exact Sorted.cons x y s hxy hs
      · -- hxy : ¬ x ≤ y
        rw [insert, ite_eq_right hxy] -- or: `simp [insert, hxy]`
        -- ⊢ Sorted (· ≤ ·) (if x ≤ y then x :: y :: s else y :: insert x s)
        -- ⊢ Sorted (· ≤ ·) (y :: insert x s)
        have hyx : y ≤ x := le_of_not_ge hxy
        cases s with
        | nil =>
            -- ⊢ Sorted (· ≤ ·) (y :: insert x [])
            -- Modulo definition of `insert|1`:
            -- ⊢ Sorted (· ≤ ·) (y :: [x])
            exact Sorted.cons y x [] hyx (Sorted.singleton x)
        | cons z t =>
            cases hs with
            | cons _ _ _ hyz hzt =>
                -- hyz : y ≤ z
                -- hzt : Sorted (· ≤ ·) (z :: t)
                by_cases hxz : x ≤ z
                · rw [insert, ite_eq_left hxz] -- or: `simp [insert, hxz]`
                  -- ⊢ Sorted (· ≤ ·) (y :: if x ≤ z then x :: z :: t else z :: insert x t)
                  -- ⊢ Sorted (· ≤ ·) (y :: x :: z :: t)
                  exact Sorted.cons y x (z :: t) hyx (Sorted.cons x z t hxz hzt)
                · rw [insert, ite_eq_right hxz]
                  -- ⊢ Sorted (· ≤ ·) (y :: if x ≤ z then x :: z :: t else z :: insert x t)
                  -- ⊢ Sorted (· ≤ ·) (y :: insert x (z :: t))
                  have h : Sorted (· ≤ ·) (insert x (z :: t)) := ih hzt
                  rw [insert, ite_eq_right hxz] at h -- or: `simp [insert, hxz] at h`
                  -- h : Sorted (· ≤ ·) (if x ≤ z then x :: z :: t else z :: insert x t)
                  -- h : Sorted (· ≤ ·) (z :: insert x t)
                  exact Sorted.cons y z (insert x t) hyz h

end InsertionSort
