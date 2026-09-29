import Mathlib.Order.Basic -- Importing here type class `LinearOrder`

namespace MyLists -- To avoid captures from Mathlib

def cat {α : Type} (l1 : List α) (l2 : List α) : List α :=
  match l1 with
  | []     => l2
  | x :: l => x :: cat l l2

theorem CatAssoc {α : Type} (s : List α) (t : List α) (u : List α) :
  cat s (cat t u) = cat (cat s t) u :=
  by induction s with
  | nil => calc
      cat [] (cat t u)
        = cat t u          := rfl -- -> cat|1
      _ = cat (cat [] t) u := rfl -- <- cat|1
  | cons x s ih => calc
      cat (x :: s) (cat t u)
        = x :: cat s (cat t u)   := rfl -- -> cat|2
      _ = x :: cat (cat s t) u   := by rw [ih]
      _ = cat (cat (x :: s) t) u := rfl -- <- cat|2

def rev' {α : Type} : List α -> List α
| []     => []
| x :: s => cat (rev' s) [x]

theorem CatNil {α : Type} (s : List α) : cat s [] = s :=
  by induction s with
  | nil => calc
      cat [] [] = [] := rfl -- -> cat|1
  | cons x s ih => calc
      cat (x :: s) []
        = x :: cat s [] := rfl -- -> cat|2
      _ = x :: s        := by rw [ih]

theorem CatRev {α : Type} (s : List α) (t : List α) :
  cat (rev' t) (rev' s) = rev' (cat s t) :=
  by induction s with
  | nil => calc
      cat (rev' t) (rev' [])
        = cat (rev' t) []    := rfl -- -> rev'|1
      _ = rev' t             := by rw [CatNil]
      _ = rev' (cat [] t)    := rfl -- -> cat|1
  | cons x s ih => calc
      cat (rev' t) (rev' (x :: s))
        = cat (rev' t) (cat (rev' s) [x]) := rfl -- -> rev'|2
      _ = cat (cat (rev' t) (rev' s)) [x] := by rw [CatAssoc]
      _ = cat (rev' (cat s t)) [x]        := by rw [ih]
      _ = rev' (x :: cat s t)             := rfl -- <- rev'|2
      _ = rev' (cat (x :: s) t)           := rfl -- <- cat|2

theorem Inv {α : Type} (s : List α) : rev' (rev' s) = s :=
  by induction s with
  | nil => calc
      rev' (rev' [])
        = rev' [] := rfl -- -> rev'|1
      _ = []      := rfl -- -> rev'|1
  | cons x s ih => calc
      rev' (rev' (x :: s))
        = rev' (cat (rev' s) [x])        := rfl -- -> rev'|2
      _ = cat (rev' [x]) (rev' (rev' s)) := by rw [<- CatRev]
      _ = cat (rev' [x]) s               := by rw [ih]
      _ = cat (cat (rev' []) [x]) s      := rfl -- -> rev'|2
      _ = cat (cat [] [x]) s             := rfl -- -> rev'|1
      _ = cat [x] s                      := rfl -- -> cat|1
      _ = x :: cat [] s                  := rfl -- -> cat|2
      _ = x :: s                         := rfl -- -> cat|1

def rcat {α : Type} (s : List α) (t : List α) : List α :=
  match s with
  | []     => t
  | x :: s => rcat s (x :: t)

def rev {α : Type} (s : List α) : List α := rcat s []

theorem RevCat {α : Type} (s : List α) (t : List α)
  : rcat s t = cat (rev s) t :=
  by induction s generalizing t with
  | nil => calc
      rcat [] t
        = t                  := rfl -- -> rcat|1
      _ = cat [] t           := rfl -- <- cat|1
      _ = cat (rcat [] []) t := rfl -- <- rcat|1
      _ = cat (rev []) t     := rfl -- <- rev
  | cons x s ih => calc
      rcat (x :: s) t
        = rcat s (x :: t)             := rfl -- -> rcat|2
      _ = cat (rev s) (x :: t)        := by rw [ih (x :: t)]
      _ = cat (rev s) (x :: cat [] t) := rfl -- <- cat|1
      _ = cat (rev s) (cat [x] t)     := rfl -- <- cat|2
      _ = cat (cat (rev s) [x]) t     := by rw [CatAssoc]
      _ = cat (rcat s [x]) t          := by rw [<- ih [x]]
      _ = cat (rcat (x :: s) []) t    := rfl -- <- rcat|2
      _ = cat (rev (x :: s)) t        := rfl -- rev

theorem EqRev {α : Type} (s : List α) : rev' s = rev s :=
  by induction s with
  | nil => calc
      rev' []
        = []         := rfl -- -> rev'|1
      _ = rcat [] [] := rfl -- <- rcat|1
      _ = rev []     := rfl -- <- rev
  | cons x s ih => calc
      rev' (x :: s)
        = cat (rev' s) [x]  := rfl -- <- rev'|2
      _ = cat (rev s) [x]   := by rw [ih]
      _ = rcat s [x]        := by rw [<- RevCat]
      _ = rcat (x :: s) []  := rfl -- <- rcat|2
      _ = rev (x :: s)      := rfl -- <- rev

end MyLists
