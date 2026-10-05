import Mathlib.Order.Basic -- Importing here type class `LinearOrder`

/-! Redefinition of `List` for educational purposes -/
namespace MyList -- To avoid captures from Mathlib

def cat {α : Type} (s : List α) (t : List α) : List α :=
  match s with
  | []     => t
  | x :: s => x :: cat s t

theorem cat.nil {α : Type} (l : List α) : cat [] l = l := rfl

theorem cat.cons {α : Type} (x : α) (s t : List α) :
  cat (x :: s) t = x :: cat s t := rfl

/-! Associativity of list concatenation -/
theorem CatAssoc {α : Type} (s t u : List α) :
  cat s (cat t u) = cat (cat s t) u :=
  by induction s with
  | nil => calc
      cat [] (cat t u)
        = cat t u          := by conv => lhs; rw [cat.nil]
      _ = cat (cat [] t) u := by conv => rhs; rw [cat.nil]
  | cons x s ih => calc
      cat (x :: s) (cat t u)
        = x :: cat s (cat t u)   := by conv => lhs; rw [cat.cons]
      _ = x :: cat (cat s t) u   := by conv => lhs; rw [ih]
      _ = cat (x :: cat s t) u   := by conv => rhs; rw [cat.cons]
      _ = cat (cat (x :: s) t) u := by conv => rhs; rw [cat.cons]

/-! Right identity of concatenation -/
theorem CatNil {α : Type} (s : List α) : cat s [] = s :=
  by induction s with
  | nil => calc
      cat [] [] = [] := by conv => lhs; rw [cat.nil]
  | cons x s ih => calc
      cat (x :: s) []
        = x :: cat s [] := by conv => lhs; rw [cat.cons]
      _ = x :: s        := by conv => lhs; rw [ih]

/-! Worst-case quadratic reversal -/
def rev' {α : Type} : List α -> List α
| []     => []
| x :: s => cat (rev' s) [x]

theorem rev'.nil {α : Type} : rev' ([] : List α) = [] := rfl

theorem rev'.cons {α : Type} (x : α) (s : List α) :
  rev' (x :: s) = cat (rev' s) [x] := rfl

theorem CatRev {α : Type} (s t : List α) :
  cat (rev' t) (rev' s) = rev' (cat s t) :=
  by induction s with
  | nil => calc
      cat (rev' t) (rev' [])
        = cat (rev' t) []    := by conv => lhs; rw [rev'.nil]
      _ = rev' t             := by conv => lhs; rw [CatNil]
      _ = rev' (cat [] t)    := by conv => rhs; rw [cat.nil]
  | cons x s ih => calc
      cat (rev' t) (rev' (x :: s))
        = cat (rev' t) (cat (rev' s) [x]) := by conv => lhs; rw [rev'.cons]
      _ = cat (cat (rev' t) (rev' s)) [x] := by conv => lhs; rw [CatAssoc]
      _ = cat (rev' (cat s t)) [x]        := by conv => lhs; rw [ih]
      _ = rev' (x :: cat s t)             := by conv => rhs; rw [rev'.cons]
      _ = rev' (cat (x :: s) t)           := by conv => rhs; rw [cat.cons]

/-! Involution -/
theorem Inv {α : Type} (s : List α) : rev' (rev' s) = s :=
  by induction s with
  | nil => calc
      rev' (rev' [])
        = rev' [] := by conv => lhs; rw [rev'.nil]
      _ = []      := by conv => lhs; rw [rev'.nil]
  | cons x s ih => calc
      rev' (rev' (x :: s))
        = rev' (cat (rev' s) [x])        := by conv => lhs; rw [rev'.cons]
      _ = cat (rev' [x]) (rev' (rev' s)) := by conv => rhs; rw [CatRev]
      _ = cat (rev' [x]) s               := by conv => lhs; rw [ih]
      _ = cat (cat (rev' []) [x]) s      := by conv => lhs; rw [rev'.cons]
      _ = cat (cat [] [x]) s             := by conv => lhs; rw [rev'.nil]
      _ = cat [x] s                      := by conv => lhs; rw [cat.nil]
      _ = x :: cat [] s                  := by conv => lhs; rw [cat.cons]
      _ = x :: s                         := by conv => lhs; rw [cat.nil]

/-! Reverse and concatenate -/
def rcat {α : Type} (s t : List α) : List α :=
  match s with
  | []     => t
  | x :: s => rcat s (x :: t)

theorem rcat.nil {α : Type} (t : List α) : rcat [] t = t := rfl

theorem rcat.cons {α : Type} (x : α) (s t : List α) :
  rcat (x :: s) t = rcat s (x :: t) := rfl

/-! Worst-case linear costs reveral -/
def rev {α : Type} (s : List α) : List α := rcat s []

/-! Reverse and concatenate it is -/
theorem RevCat {α : Type} (s t : List α) : rcat s t = cat (rev s) t :=
  by induction s generalizing t with
  | nil => calc
      rcat [] t
        = t                  := by conv => lhs; rw [rcat.nil]
      _ = cat [] t           := by conv => rhs; rw [cat.nil]
      _ = cat (rcat [] []) t := by conv => rhs; rw [rcat.nil]
      _ = cat (rev []) t     := by conv => rhs; rw [rev]
  | cons x s ih => calc
      rcat (x :: s) t
        = rcat s (x :: t)             := by conv => lhs; rw [rcat.cons]
      _ = cat (rev s) (x :: t)        := by conv => lhs; rw [ih (x :: t)]
      _ = cat (rev s) (x :: cat [] t) := by conv => rhs; rw [cat.nil]
      _ = cat (rev s) (cat [x] t)     := by conv => rhs; rw [cat.cons]
      _ = cat (cat (rev s) [x]) t     := by conv => lhs; rw [CatAssoc]
      _ = cat (rcat s [x]) t          := by conv => rhs; rw [ih [x]]
      _ = cat (rcat (x :: s) []) t    := by conv => rhs; rw [rcat.cons]
      _ = cat (rev (x :: s)) t        := by conv => rhs; rw [rev]

theorem EqRev {α : Type} (s : List α) : rev' s = rev s :=
  by induction s with
  | nil => calc
      rev' []
        = []         := by conv => lhs; rw [rev'.nil]
      _ = rcat [] [] := by conv => rhs; rw [rcat.nil]
      _ = rev []     := by conv => rhs; rw [rev]
  | cons x s ih => calc
      rev' (x :: s)
        = cat (rev' s) [x]  := by conv => lhs; rw [rev'.cons]
      _ = cat (rev s) [x]   := by conv => lhs; rw [ih]
      _ = rcat s [x]        := by conv => rhs; rw [RevCat]
      _ = rcat (x :: s) []  := by conv => rhs; rw [rcat.cons]
      _ = rev (x :: s)      := by conv => rhs; rw [rev]

theorem Rcat {α : Type} (s t u : List α) :
  rcat s (rcat t u) = rcat (cat t s) u :=
  calc
    rcat s (rcat t u)
      = rcat s (cat (rev t) u)        := by conv => lhs; rw [RevCat t u]
    _ = rcat s (cat (rev' t) u)       := by conv => rhs; rw [EqRev]
    _ = cat (rev s) (cat (rev' t) u)  := by conv => lhs; rw [RevCat]
    _ = cat (rev' s) (cat (rev' t) u) := by conv => rhs; rw [EqRev]
    _ = cat (cat (rev' s) (rev' t)) u := by conv => lhs; rw [CatAssoc]
    _ = cat (rev' (cat t s)) u        := by conv => lhs; rw [CatRev]
    _ = cat (rev (cat t s)) u         := by conv => lhs; rw [EqRev]
    _ = rcat (cat t s) u              := by conv => rhs; rw [RevCat]

end MyList
