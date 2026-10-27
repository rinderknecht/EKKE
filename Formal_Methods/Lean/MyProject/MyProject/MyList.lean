import MyProject.Macros

/-! Redefinition of `List` for educational purposes -/
namespace MyList -- To avoid captures from Mathlib

def cat {α : Type} : List α -> List α -> List α
| [],     t => t
| x :: s, t => x :: cat s t

lemma cat.nil {α : Type} (t : List α) : cat [] t = t := rfl

lemma cat.cons {α : Type} (x : α) (s t : List α) :
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
def rev₀ {α : Type} : List α -> List α
| []     => []
| x :: s => cat (rev₀ s) [x]

lemma rev₀.nil {α : Type} : rev₀ ([] : List α) = [] := rfl

lemma rev₀.cons {α : Type} (x : α) (s : List α) :
  rev₀ (x :: s) = cat (rev₀ s) [x] := rfl

attribute [irreducible] rev₀

theorem CatRev {α : Type} (s t : List α) :
  cat (rev₀ t) (rev₀ s) = rev₀ (cat s t) := by
  induction s with
  | nil => calc
      cat (rev₀ t) (rev₀ [])
        = cat (rev₀ t) []    := at [1,2] use rev₀.nil
      _ = rev₀ t             := CatNil (rev₀ t)
      _ = rev₀ (cat [] t)    := at [2,1] use cat.nil t
  | cons x s ih =>
      guard_hyp ih : cat (rev₀ t) (rev₀ s) = rev₀ (cat s t)
      show cat (rev₀ t) (rev₀ (x :: s)) = rev₀ (cat (x :: s) t)
      calc
        cat (rev₀ t) (rev₀ (x :: s))
          = cat (rev₀ t) (cat (rev₀ s) [x]) := at [1,2] use rev₀.cons x s
        _ = cat (cat (rev₀ t) (rev₀ s)) [x] := CatAssoc (rev₀ t) (rev₀ s) [x]
        _ = cat (rev₀ (cat s t)) [x]        := at [1,1] use ih
        _ = rev₀ (x :: cat s t)             := at [2] use rev₀.cons x (cat s t)
        _ = rev₀ (cat (x :: s) t)           := at [2,1] use cat.cons x s t

/-! Involution -/
theorem Inv {α : Type} (s : List α) : rev₀ (rev₀ s) = s := by
  induction s with
  | nil => calc
      rev₀ (rev₀ [])
        = rev₀ [] := at [1,1] use rev₀.nil
      _ = []      := rev₀.nil
  | cons x s ih =>
      guard_hyp ih : rev₀ (rev₀ s) = s
      show rev₀ (rev₀ (x :: s)) = x :: s
      calc
        rev₀ (rev₀ (x :: s))
          = rev₀ (cat (rev₀ s) [x])        := at [1,1] use rev₀.cons x s
        _ = cat (rev₀ [x]) (rev₀ (rev₀ s)) := at [2] use CatRev (rev₀ s) [x]
        _ = cat (rev₀ [x]) s               := at [1,2] use ih
        _ = cat (cat (rev₀ []) [x]) s      := at [1,1] use rev₀.cons x []
        _ = cat (cat [] [x]) s             := at [1,1,1] use rev₀.nil
        _ = cat [x] s                      := at [1,1] use cat.nil [x]
        _ = x :: cat [] s                  := cat.cons x [] s
        _ = x :: s                         := at [1,2] use cat.nil s

/-! Reverse and concatenate -/
def rcat {α : Type} : List α -> List α -> List α
| [],    t  => t
| x :: s, t => rcat s (x :: t)

lemma rcat.nil {α : Type} (t : List α) : rcat [] t = t := rfl

lemma rcat.cons {α : Type} (x : α) (s t : List α) :
  rcat (x :: s) t = rcat s (x :: t) := rfl

/-! Reversal with linear worst-case -/
def rev {α : Type} (s : List α) : List α := rcat s []

lemma rev.def {α : Type} (s : List α) : rev s = rcat s [] := rfl

attribute [irreducible] rcat rev

/-! Reverse and concatenate -/
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

theorem EqRev {α : Type} (s : List α) : rev₀ s = rev s := by
  induction s with
  | nil => calc
      rev₀ []
        = []         := rev₀.nil
      _ = rcat [] [] := at [2] use rcat.nil []
      _ = rev []     := at [2] use rev.def []
  | cons x s ih =>
      guard_hyp ih : rev₀ s = rev s
      show rev₀ (x :: s) = rev (x :: s)
      calc
        rev₀ (x :: s)
          = cat (rev₀ s) [x]  := rev₀.cons x s
        _ = cat (rev s) [x]   := at [1,1] use ih
        _ = rcat s [x]        := at [2] use RevCat s [x]
        _ = rcat (x :: s) []  := at [2] use rcat.cons x s []
        _ = rev (x :: s)      := at [2] use rev.def (x :: s)

theorem InvRev {α : Type} (s : List α) : rev (rev s) = s := by
  calc
    rev (rev s)
      = rev (rev₀ s)  := at [2,1] use EqRev s
    _ = rev₀ (rev₀ s) := at [2] use EqRev (rev₀ s)
    _ = s             := Inv s

theorem Rcat {α : Type} (s t u : List α) :
  rcat s (rcat t u) = rcat (cat t s) u :=
  calc
    rcat s (rcat t u)
      = rcat s (cat (rev t) u)        := at [1,2] use RevCat t u
    _ = rcat s (cat (rev₀ t) u)       := at [2,2,1] use EqRev t
    _ = cat (rev s) (cat (rev₀ t) u)  := RevCat s (cat (rev₀ t) u)
    _ = cat (rev₀ s) (cat (rev₀ t) u) := at [2,1] use EqRev s
    _ = cat (cat (rev₀ s) (rev₀ t)) u := CatAssoc (rev₀ s) (rev₀ t) u
    _ = cat (rev₀ (cat t s)) u        := at [1,1] use CatRev t s
    _ = cat (rev (cat t s)) u         := at [1,1] use EqRev (cat t s)
    _ = rcat (cat t s) u              := at [2] use RevCat (cat t s) u

end MyList
