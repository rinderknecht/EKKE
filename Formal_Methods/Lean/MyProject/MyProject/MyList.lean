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

attribute [irreducible] cat

/-! Associativity of list concatenation -/
theorem CatAssoc {α : Type} (s t u : List α) :
  cat s (cat t u) = cat (cat s t) u :=
  by induction s with
  | nil => calc
      cat [] (cat t u)
        = cat t u          := cat.nil (cat t u)
      _ = cat (cat [] t) u := by conv => enter [2,1]; exact cat.nil t
  | cons x s ih => calc
      cat (x :: s) (cat t u)
        = x :: cat s (cat t u)   := cat.cons x s (cat t u)
      _ = x :: cat (cat s t) u   := by conv => enter [1,2]; exact ih
      _ = cat (x :: cat s t) u   := Eq.symm (cat.cons x (cat s t) u)
      _ = cat (cat (x :: s) t) u := by conv => enter [2,1]; exact cat.cons x s t

/-! Right identity of concatenation -/
theorem CatNil {α : Type} (s : List α) : cat s [] = s :=
  by induction s with
  | nil => calc
      cat [] [] = [] := cat.nil []
  | cons x s ih => calc
      cat (x :: s) []
        = x :: cat s [] := cat.cons x s []
      _ = x :: s        := by conv => enter [1,2]; exact ih

/-! Worst-case quadratic reversal -/
def rev' {α : Type} : List α -> List α
| []     => []
| x :: s => cat (rev' s) [x]

theorem rev'.nil {α : Type} : rev' ([] : List α) = [] := rfl

theorem rev'.cons {α : Type} (x : α) (s : List α) :
  rev' (x :: s) = cat (rev' s) [x] := rfl

attribute [irreducible] rev'

theorem CatRev {α : Type} (s t : List α) :
  cat (rev' t) (rev' s) = rev' (cat s t) :=
  by induction s with
  | nil => calc
      cat (rev' t) (rev' [])
        = cat (rev' t) []    := by conv => enter [1,2]; exact rev'.nil
      _ = rev' t             := CatNil (rev' t)
      _ = rev' (cat [] t)    := by conv => enter [2,1]; exact cat.nil t
  | cons x s ih => calc
      cat (rev' t) (rev' (x :: s))
        = cat (rev' t) (cat (rev' s) [x]) := by conv => enter [1,2]; exact rev'.cons x s
      _ = cat (cat (rev' t) (rev' s)) [x] := CatAssoc (rev' t) (rev' s) [x]
      _ = cat (rev' (cat s t)) [x]        := by conv => enter [1,1]; exact ih
      _ = rev' (x :: cat s t)             := Eq.symm (rev'.cons x (cat s t))
      _ = rev' (cat (x :: s) t)           := by conv => enter [2,1]; exact cat.cons x s t

/-! Involution -/
theorem Inv {α : Type} (s : List α) : rev' (rev' s) = s :=
  by induction s with
  | nil => calc
      rev' (rev' [])
        = rev' [] := by conv => enter [1,1]; exact rev'.nil
      _ = []      := rev'.nil
  | cons x s ih => calc
      rev' (rev' (x :: s))
        = rev' (cat (rev' s) [x])        := by conv => enter [1,1]; exact rev'.cons x s
      _ = cat (rev' [x]) (rev' (rev' s)) := Eq.symm (CatRev (rev' s) [x])
      _ = cat (rev' [x]) s               := by conv => enter [1,2]; exact ih
      _ = cat (cat (rev' []) [x]) s      := by conv => enter [1,1]; exact rev'.cons x []
      _ = cat (cat [] [x]) s             := by conv => enter [1,1,1]; exact rev'.nil
      _ = cat [x] s                      := by conv => enter [1,1]; exact cat.nil [x]
      _ = x :: cat [] s                  := cat.cons x [] s
      _ = x :: s                         := by conv => enter [1,2]; exact cat.nil s

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

theorem rev.def {α : Type} (s : List α) : rev s = rcat s [] := rfl

attribute [irreducible] rcat rev

/-! Reverse and concatenate it is -/
theorem RevCat {α : Type} (s t : List α) : rcat s t = cat (rev s) t :=
  by induction s generalizing t with
  | nil => calc
      rcat [] t
        = t                  := rcat.nil t
      _ = cat [] t           := Eq.symm (cat.nil t)
      _ = cat (rcat [] []) t := by conv => enter [2,1]; exact rcat.nil []
      _ = cat (rev []) t     := by conv => enter [2,1]; exact rev.def []
  | cons x s ih => calc
      rcat (x :: s) t
        = rcat s (x :: t)             := rcat.cons x s t
      _ = cat (rev s) (x :: t)        := ih (x :: t)
      _ = cat (rev s) (x :: cat [] t) := by conv => enter [2,2,2]; exact cat.nil t
      _ = cat (rev s) (cat [x] t)     := by conv => enter [2,2]; exact cat.cons x [] t
      _ = cat (cat (rev s) [x]) t     := CatAssoc (rev s) [x] t
      _ = cat (rcat s [x]) t          := by conv => enter [2,1]; exact ih [x]
      _ = cat (rcat (x :: s) []) t    := by conv => enter [2,1]; exact rcat.cons x s []
      _ = cat (rev (x :: s)) t        := by conv => enter [2,1]; exact rev.def (x :: s)

theorem EqRev {α : Type} (s : List α) : rev' s = rev s :=
  by induction s with
  | nil => calc
      rev' []
        = []         := rev'.nil
      _ = rcat [] [] := Eq.symm (rcat.nil [])
      _ = rev []     := Eq.symm (rev.def [])
  | cons x s ih => calc
      rev' (x :: s)
        = cat (rev' s) [x]  := rev'.cons x s
      _ = cat (rev s) [x]   := by conv => enter [1,1]; exact ih
      _ = rcat s [x]        := Eq.symm (RevCat s [x])
      _ = rcat (x :: s) []  := Eq.symm (rcat.cons x s [])
      _ = rev (x :: s)      := Eq.symm (rev.def (x :: s))

theorem Rcat {α : Type} (s t u : List α) :
  rcat s (rcat t u) = rcat (cat t s) u :=
  calc
    rcat s (rcat t u)
      = rcat s (cat (rev t) u)        := by conv => enter [1,2]; exact RevCat t u
    _ = rcat s (cat (rev' t) u)       := by conv => enter [2,2,1]; exact EqRev t
    _ = cat (rev s) (cat (rev' t) u)  := RevCat s (cat (rev' t) u)
    _ = cat (rev' s) (cat (rev' t) u) := by conv => enter [2,1]; exact EqRev s
    _ = cat (cat (rev' s) (rev' t)) u := CatAssoc (rev' s) (rev' t) u
    _ = cat (rev' (cat t s)) u        := by conv => enter [1,1]; exact CatRev t s
    _ = cat (rev (cat t s)) u         := by conv => enter [1,1]; exact EqRev (cat t s)
    _ = rcat (cat t s) u              := Eq.symm (RevCat (cat t s) u)

end MyList
