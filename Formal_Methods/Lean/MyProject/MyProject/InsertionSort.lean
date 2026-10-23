import Mathlib.Order.Basic
import MyProject.Macros

/-! Insertion sort -/
namespace InsertionSort -- To avoid captures from Mathlib

/-- Permutations on lists

  We define a permutation on a list as a composition of transpositions
  on the elements of that list, that is, exchanges of adjacent
  keys. The inductive proposition `Perm s t` means that `s` is a
  permutation of `t`.
-/
inductive Perm {α : Type} : List α -> List α → Prop where
| nil                         : Perm [] []
| cons (x : α) (s t : List α) : Perm s t -> Perm (x :: s) (x :: t)
| swap (x y : α) (s : List α) : Perm (x :: y :: s) (y :: x :: s)
| trans (s t u : List α)      : Perm s t -> Perm t u -> Perm s u

set_option linter.style.show false in
lemma Perm.symmetry {α : Type} (s t : List α) : Perm s t -> Perm t s := by
  intro h
  guard_hyp h : Perm s t
  induction h with
  | nil =>
      show Perm [] []; exact Perm.nil
  | cons x s t _ ih =>
      show Perm (x :: t) (x :: s); exact Perm.cons x t s ih
  | swap x y s =>
      show Perm (y :: x :: s) (x :: y :: s); exact Perm.swap y x s
  | trans s t u _ _ ih1 ih2 =>
      show Perm u s; exact Perm.trans u t s ih2 ih1

lemma Perm.reflexivity {α : Type} (s : List α) : Perm s s := by
  induction s with
  | nil         => show Perm [] []; exact Perm.nil
  | cons x s ih => show Perm (x :: s) (x :: s); exact Perm.cons x s s ih

/-- Insertion in non-decreasing order -/
def insert {α : Type} [LinearOrder α] (x : α) : List α → List α
| []     => [x]
| y :: s => if x ≤ y then x :: y :: s else y :: insert x s

theorem insert.nil {α : Type} [LinearOrder α] (x : α) : insert x [] = [x] := rfl

theorem insert.cons {α : Type} [LinearOrder α] (x y : α) (s : List α) :
  insert x (y :: s) = if x ≤ y then x :: y :: s else y :: insert x s := rfl

attribute [irreducible] insert

lemma Insert.extends {α : Type} [LinearOrder α] (x : α) (s : List α) :
  Perm (insert x s) (x :: s) := by
  induction s with
  | nil =>
     show Perm (insert x []) [x]
     at [1] use insert.nil x
     show Perm [x] [x]
     exact Perm.reflexivity [x]
  | cons y s ih =>
      guard_hyp ih : Perm (insert x s) (x :: s)
      show Perm (insert x (y :: s)) (x :: y :: s)
      by_cases hxy : x ≤ y
      · -- ite_eq_left (h : p) : (if p then a else b) = a --- `h` is a proof and `p` a proposition
        -- ite_eq_left hxy : (if x ≤ y then x :: y :: s else y :: insert x s) = x :: y :: s
        at [1] use Eq.trans (insert.cons x y s) (ite_eq_left hxy)
        show Perm (x :: y :: s) (x :: y :: s)
        exact Perm.reflexivity (x :: y :: s)
      · guard_hyp hxy : ¬ x ≤ y
        -- ite_eq_right (h : p) : (if p then a else b) = b --- `h` is a proof and `p` a proposition
        -- ite_eq_right hxy : (if x ≤ y then x :: y :: s else y :: insert x s) = y :: insert x s
        at [1] use Eq.trans (insert.cons x y s) (ite_eq_right hxy)
        show Perm (y :: insert x s) (x :: y :: s)
        have h : Perm (y :: insert x s) (y :: x :: s) := Perm.cons y (insert x s) (x :: s) ih
        have h' : Perm (y :: x :: s) (x :: y :: s) := Perm.symmetry _ _ (Perm.swap x y s)
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

set_option linter.style.show false in
lemma Insert.preserves_order {α : Type} [LinearOrder α] (x : α) (s : List α) :
  Sorted s → Sorted (insert x s) := by
  induction s with
  | nil =>
      show Sorted [] → Sorted (insert x [])
      intro _
      show Sorted (insert x [])
      at [1] use insert.nil x
      show Sorted [x]
      exact Ordered.singleton x
  | cons y s ih =>
      guard_hyp ih : Sorted s → Sorted (insert x s)
      show Sorted (y :: s) → Sorted (insert x (y :: s))
      intro hs
      guard_hyp hs : Sorted (y :: s)
      show Sorted (insert x (y :: s))
      by_cases hxy : x ≤ y
      · -- ite_eq_left hxy : (if x ≤ y then x :: y :: s else y :: insert x s) = x :: y :: s
        at [1] use Eq.trans (insert.cons x y s) (ite_eq_left hxy)
        show Sorted (x :: y :: s)
        exact Ordered.cons x y s hxy hs
      · guard_hyp hxy : ¬ x ≤ y
        at [1] use Eq.trans (insert.cons x y s) (ite_eq_right hxy)
        show Sorted (y :: insert x s)
        have hyx : y ≤ x := le_of_not_ge hxy
        cases s with
        | nil =>
            show Sorted (y :: insert x [])
            at [1,2] use insert.nil x
            show Sorted (y :: [x])
            exact Ordered.cons y x [] hyx (Ordered.singleton x)
        | cons z t =>
            show Sorted (y :: insert x (z :: t))
            guard_hyp hs : Sorted (y :: z :: t)
            cases hs with
            | cons _ _ _ hyz hzt =>
                guard_hyp hyz : y ≤ z
                guard_hyp hzt : Ordered (· ≤ ·) (z :: t) -- `Ordered` due `cases hs with`.
                by_cases hxz : x ≤ z
                · at [1,2] use Eq.trans (insert.cons x z t) (ite_eq_left hxz)
                  show Sorted (y :: x :: z :: t)
                  exact Ordered.cons y x (z :: t) hyx (Ordered.cons x z t hxz hzt)
                · at [1,2] use Eq.trans (insert.cons x z t) (ite_eq_right hxz)
                  show Sorted (y :: z :: insert x t)
                  have h : Sorted (insert x (z :: t)) := ih hzt
                  at [1] in h use Eq.trans (insert.cons x z t) (ite_eq_right hxz)
                  guard_hyp h : Sorted (z :: insert x t)
                  show Sorted (y :: z :: insert x t)
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
  Sorted (sort s) ∧ Perm (sort s) s := by
  induction s with
  | nil =>
      show Sorted (sort []) ∧ Perm (sort []) []
      constructor
      · show Sorted (sort [])
        at [1] use sort.nil
        show Sorted []
        exact Ordered.nil
      · show Perm (sort []) []
        at [1] use sort.nil
        show Perm [] []
        exact Perm.nil
  | cons x s ih =>
      guard_hyp ih : Sorted (sort s) ∧ Perm (sort s) s
      show Sorted (sort (x :: s)) ∧ Perm (sort (x :: s)) (x :: s)
      constructor
      · show Sorted (sort (x :: s))
        at [1] use sort.cons x s
        show Sorted (insert x (sort s))
        exact Insert.preserves_order x (sort s) ih.1
      · show Perm (sort (x :: s)) (x :: s)
        at [1] use sort.cons x s
        show Perm (insert x (sort s)) (x :: s)
        have h : Perm (insert x (sort s)) (x :: sort s) := Insert.extends x (sort s)
        have h' : Perm (x :: sort s) (x :: s) := Perm.cons x (sort s) s ih.2
        exact Perm.trans _ _ _ h h'

end InsertionSort
