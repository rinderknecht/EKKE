import MyProject.Macros

/-! Redefinition of `List` for educational purposes -/
namespace MyList -- To avoid captures from Mathlib

def cat {α : Type} : List α -> List α -> List α
| [],     t => t
| x :: s, t => x :: cat s t

theorem cat.nil {α : Type} (t : List α) : cat [] t = t := rfl

theorem cat.cons {α : Type} (x : α) (s t : List α) :
  cat (x :: s) t = x :: cat s t := rfl

attribute [irreducible] cat

/-! Right identity of concatenation -/
theorem CatNil {α : Type} (s : List α) : cat s [] = s := by
  induction s with
  | nil => calc
      cat [] [] = [] := cat.nil []
  | cons x s ih => calc
      cat (x :: s) []
        = x :: cat s [] := cat.cons x s []
      _ = x :: s        := at [1,2] use ih

/-! Associativity of list concatenation -/
theorem CatAssoc {α : Type} (s t u : List α) :
  cat s (cat t u) = cat (cat s t) u := by
  induction s with
  | nil => calc
      cat [] (cat t u)
        = cat t u          := cat.nil (cat t u)
      _ = cat (cat [] t) u := at [2,1] use cat.nil t
  | cons x s ih =>
      guard_hyp ih : cat s (cat t u) = cat (cat s t) u
      show cat (x :: s) (cat t u) = cat (cat (x :: s) t) u
      calc
        cat (x :: s) (cat t u)
          = x :: cat s (cat t u)   := cat.cons x s (cat t u)
        _ = x :: cat (cat s t) u   := at [1,2] use ih
        _ = cat (x :: cat s t) u   := at [2] use cat.cons x (cat s t) u
        _ = cat (cat (x :: s) t) u := at [2,1] use cat.cons x s t

/-! Worst-case quadratic reversal -/
def rev' {α : Type} : List α -> List α
| []     => []
| x :: s => cat (rev' s) [x]

theorem rev'.nil {α : Type} : rev' ([] : List α) = [] := rfl

theorem rev'.cons {α : Type} (x : α) (s : List α) :
  rev' (x :: s) = cat (rev' s) [x] := rfl

attribute [irreducible] rev'

theorem CatRev {α : Type} (s t : List α) :
  cat (rev' t) (rev' s) = rev' (cat s t) := by
  induction s with
  | nil => calc
      cat (rev' t) (rev' [])
        = cat (rev' t) []    := at [1,2] use rev'.nil
      _ = rev' t             := CatNil (rev' t)
      _ = rev' (cat [] t)    := at [2,1] use cat.nil t
  | cons x s ih =>
      guard_hyp ih : cat (rev' t) (rev' s) = rev' (cat s t)
      show cat (rev' t) (rev' (x :: s)) = rev' (cat (x :: s) t)
      calc
        cat (rev' t) (rev' (x :: s))
          = cat (rev' t) (cat (rev' s) [x]) := at [1,2] use rev'.cons x s
        _ = cat (cat (rev' t) (rev' s)) [x] := CatAssoc (rev' t) (rev' s) [x]
        _ = cat (rev' (cat s t)) [x]        := at [1,1] use ih
        _ = rev' (x :: cat s t)             := at [2] use rev'.cons x (cat s t)
        _ = rev' (cat (x :: s) t)           := at [2,1] use cat.cons x s t

/-! Involution -/
theorem Inv {α : Type} (s : List α) : rev' (rev' s) = s := by
  induction s with
  | nil => calc
      rev' (rev' [])
        = rev' [] := at [1,1] use rev'.nil
      _ = []      := rev'.nil
  | cons x s ih =>
      guard_hyp ih : rev' (rev' s) = s
      show rev' (rev' (x :: s)) = x :: s
      calc
        rev' (rev' (x :: s))
          = rev' (cat (rev' s) [x])        := at [1,1] use rev'.cons x s
        _ = cat (rev' [x]) (rev' (rev' s)) := at [2] use CatRev (rev' s) [x]
        _ = cat (rev' [x]) s               := at [1,2] use ih
        _ = cat (cat (rev' []) [x]) s      := at [1,1] use rev'.cons x []
        _ = cat (cat [] [x]) s             := at [1,1,1] use rev'.nil
        _ = cat [x] s                      := at [1,1] use cat.nil [x]
        _ = x :: cat [] s                  := cat.cons x [] s
        _ = x :: s                         := at [1,2] use cat.nil s

/-! Reverse and concatenate -/
def rcat {α : Type} : List α -> List α -> List α
| [], t     => t
| x :: s, t => rcat s (x :: t)

theorem rcat.nil {α : Type} (t : List α) : rcat [] t = t := rfl

theorem rcat.cons {α : Type} (x : α) (s t : List α) :
  rcat (x :: s) t = rcat s (x :: t) := rfl

/-! Worst-case linear costs reveral -/
def rev {α : Type} (s : List α) : List α := rcat s []

theorem rev.def {α : Type} (s : List α) : rev s = rcat s [] := rfl

attribute [irreducible] rcat rev

/-! Reverse and concatenate it is -/
theorem RevCat {α : Type} (s t : List α) : rcat s t = cat (rev s) t := by
  induction s generalizing t with
  | nil => calc
      rcat [] t
        = t                  := rcat.nil t
      _ = cat [] t           := at [2] use cat.nil t
      _ = cat (rcat [] []) t := at [2,1] use rcat.nil []
      _ = cat (rev []) t     := at [2,1] use rev.def []
  | cons x s ih =>
      guard_hyp ih : ∀ (t : List α), rcat s t = cat (rev s) t
      show rcat (x :: s) t = cat (rev (x :: s)) t
      calc
        rcat (x :: s) t
          = rcat s (x :: t)             := rcat.cons x s t
        _ = cat (rev s) (x :: t)        := ih (x :: t)
        _ = cat (rev s) (x :: cat [] t) := at [2,2,2] use cat.nil t
        _ = cat (rev s) (cat [x] t)     := at [2,2] use cat.cons x [] t
        _ = cat (cat (rev s) [x]) t     := CatAssoc (rev s) [x] t
        _ = cat (rcat s [x]) t          := at [2,1] use ih [x]
        _ = cat (rcat (x :: s) []) t    := at [2,1] use rcat.cons x s []
        _ = cat (rev (x :: s)) t        := at [2,1] use rev.def (x :: s)

theorem EqRev {α : Type} (s : List α) : rev' s = rev s := by
  induction s with
  | nil => calc
      rev' []
        = []         := rev'.nil
      _ = rcat [] [] := at [2] use rcat.nil []
      _ = rev []     := at [2] use rev.def []
  | cons x s ih =>
      guard_hyp ih : rev' s = rev s
      show rev' (x :: s) = rev (x :: s)
      calc
        rev' (x :: s)
          = cat (rev' s) [x]  := rev'.cons x s
        _ = cat (rev s) [x]   := at [1,1] use ih
        _ = rcat s [x]        := at [2] use RevCat s [x]
        _ = rcat (x :: s) []  := at [2] use rcat.cons x s []
        _ = rev (x :: s)      := at [2] use rev.def (x :: s)

theorem Rcat {α : Type} (s t u : List α) :
  rcat s (rcat t u) = rcat (cat t s) u :=
  calc
    rcat s (rcat t u)
      = rcat s (cat (rev t) u)        := at [1,2] use RevCat t u
    _ = rcat s (cat (rev' t) u)       := at [2,2,1] use EqRev t
    _ = cat (rev s) (cat (rev' t) u)  := RevCat s (cat (rev' t) u)
    _ = cat (rev' s) (cat (rev' t) u) := at [2,1] use EqRev s
    _ = cat (cat (rev' s) (rev' t)) u := CatAssoc (rev' s) (rev' t) u
    _ = cat (rev' (cat t s)) u        := at [1,1] use CatRev t s
    _ = cat (rev (cat t s)) u         := at [1,1] use EqRev (cat t s)
    _ = rcat (cat t s) u              := at [2] use RevCat (cat t s) u

end MyList
