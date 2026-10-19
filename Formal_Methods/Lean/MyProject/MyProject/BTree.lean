import Mathlib.Order.Basic

import MyProject.MyList

/-! Our lists -/
open MyList

/-! Binary trees -/
namespace BTree

inductive Tree (α : Type) : Type where
| ext
| int (x : α) (left right : Tree α)

-- Preorder (a.k.a. prefix) traversals

/- Worst case quadratic cost -/
def pre0 {α : Type} : Tree α -> List α
| .ext         => []
| .int x t1 t2 => x :: cat (pre0 t1) (pre0 t2)

theorem pre0.ext {α : Type} : pre0 (.ext : Tree α) = [] := rfl

theorem pre0.int {α : Type} (x : α) (t1 t2 : Tree α) :
  pre0 (.int x t1 t2) = x :: cat (pre0 t1) (pre0 t2) := rfl

attribute [irreducible] pre0

/- Worst case linear cost -/
/- Note: I could avoid naming `t` and have purely equational definitions,
   but I follow the book -/
def pre' {α : Type} (t : Tree α) (s : List α) : List α :=
  match t with
  | .ext         => s
  | .int x t1 t2 => x :: pre' t1 (pre' t2 s)

theorem pre'.ext {α : Type} (s : List α) : pre' .ext s = s := rfl

theorem pre'.int {α : Type} (s : List α) (x : α) (t1 t2 : Tree α) :
  pre' (.int x t1 t2) s = x :: pre' t1 (pre' t2 s) := rfl

def pre {α : Type} (t : Tree α) : List α := pre' t []

theorem pre.def {α : Type} (t : Tree α) : pre t = pre' t [] := rfl

attribute [irreducible] pre' pre

lemma CatPre {α : Type} (t : Tree α) (s : List α) :
  cat (pre' t []) s = pre' t s := by
  induction t generalizing s with
  | ext => calc
      cat (pre' .ext []) s
        = cat [] s         := at [1,1] use pre'.ext []
      _ = s                := cat.nil s
      _ = pre' .ext s      := at [2] use pre'.ext s
  | int x t1 t2 ih1 ih2 => calc
      -- ih1 : ∀ (s : List α), cat (pre' t1 []) s = pre' t1 s
      -- ih2 : ∀ (s : List α), cat (pre' t2 []) s = pre' t2 s
      -- ⊢ cat (pre' (.int x t1 t2) []) s = pre' (.int x t1 t2) s
     cat (pre' (.int x t1 t2) []) s
       = cat (x :: pre' t1 (pre' t2 [])) s          := at [1,1] use pre'.int [] x t1 t2
     _ = x :: cat (pre' t1 (pre' t2 [])) s          := cat.cons x (pre' t1 (pre' t2 [])) s
     _ = x :: cat (cat (pre' t1 []) (pre' t2 [])) s := at [2,2,1] use ih1 (pre' t2 [])
     _ = x :: cat (pre' t1 []) (cat (pre' t2 []) s) := at [2,2] use CatAssoc _ _ s
     _ = x :: cat (pre' t1 []) (pre' t2 s)          := at [1,2,2] use ih2 s
     _ = x :: pre' t1 (pre' t2 s)                   := at [1,2] use ih1 (pre' t2 s)
     _ = pre' (.int x t1 t2) s                      := at [2] use pre'.int s x t1 t2

/-! The two preorder traversals are equivalent -/
theorem Pre {α : Type} (t : Tree α) : pre0 t = pre t := by
  induction t with
  | ext => calc
      pre0 .ext
        = []           := pre0.ext
      _ = pre' .ext [] := at [2] use pre'.ext []
      _ = pre .ext     := at [2] use pre.def .ext
  | int x t1 t2 h1 h2 => calc
      pre0 (.int x t1 t2)
        = x :: cat (pre0 t1) (pre0 t2)       := pre0.int x t1 t2
      _ = x :: cat (pre t1) (pre0 t2)        := at [1,2,1] use h1
      _ = x :: cat (pre t1) (pre t2)         := at [1,2,2] use h2
      _ = x :: cat (pre' t1 []) (pre t2)     := at [1,2,1] use pre.def t1
      _ = x :: cat (pre' t1 []) (pre' t2 []) := at [1,2,2] use pre.def t2
      _ = x :: pre' t1 (pre' t2 [])          := at [1,2] use CatPre t1 (pre' t2 [])
      _ = pre' (.int x t1 t2) []             := at [2] use pre'.int [] x t1 t2
      _ = pre (.int x t1 t2)                 := at [2] use pre.def (.int x t1 t2)

-- Mirroring

def mir {α : Type} : Tree α -> Tree α
| .ext         => .ext
| .int x t1 t2 => .int x (mir t2) (mir t1)

theorem mir.ext {α : Type} : mir (.ext : Tree α) = .ext := rfl

theorem mir.int {α : Type} (x : α) (t1 t2 : Tree α) :
  mir (.int x t1 t2) = .int x (mir t2) (mir t1) := rfl

attribute [irreducible] mir

-- Inorder traversal

/- Note: I could avoid naming `t` and have purely equational definitions,
   but I follow the book -/
def inorder' {α : Type} (t : Tree α) (s : List α) : List α :=
  match t with
  | .ext         => s
  | .int x t1 t2 => inorder' t1 (x :: inorder' t2 s)

theorem inorder'.ext {α : Type} (s : List α) : inorder' .ext s = s := rfl

theorem inorder'.int {α : Type} (s : List α) (x : α) (t1 t2 : Tree α) :
  inorder' (.int x t1 t2) s = inorder' t1 (x :: inorder' t2 s) := rfl

def inorder {α : Type} (t : Tree α) : List α := inorder' t []

theorem inorder.def {α : Type} (t : Tree α) : inorder t = inorder' t [] := rfl

attribute [irreducible] inorder

theorem CatIn {α : Type} (t : Tree α) (s : List α) :
  cat (inorder' t []) s = inorder' t s := by
  induction t generalizing s with
  | ext => calc
      cat (inorder' .ext []) s
        = cat [] s        := at [1,1] use inorder'.ext []
      _ = s               := cat.nil s
      _ = inorder' .ext s := at [2] use inorder'.ext s
  | int x t1 t2 ih1 ih2 => calc
      -- ih1 : ∀ (s : List α), cat (inorder' t1 []) s = inorder' t1 s
      -- ih2 : ∀ (s : List α), cat (inorder' t2 []) s = inorder' t2 s
      -- ⊢ cat (inorder' (.int x t1 t2) []) s = inorder' (.int x t1 t2) s
      cat (inorder' (.int x t1 t2) []) s
        = cat (inorder' t1 (x :: inorder' t2 [])) s          := at [1,1] use inorder'.int [] x t1 t2
      _ = cat (cat (inorder' t1 []) (x :: inorder' t2 [])) s := at [2,1] use ih1 (x :: inorder' t2 [])
      _ = cat (inorder' t1 []) (cat (x :: inorder' t2 []) s) := at [2] use CatAssoc _ _ s
      _ = cat (inorder' t1 []) (x :: cat (inorder' t2 []) s) := at [1,2] use cat.cons x _ s
      _ = cat (inorder' t1 []) (x :: inorder' t2 s)          := at [1,2,2] use ih2 s
      _ = inorder' t1 (x :: inorder' t2 s)                   := ih1 (x :: inorder' t2 s)
      _ = inorder' (.int x t1 t2) s                          := at [2] use inorder'.int s x t1 t2

theorem InMir' {α : Type} (t : Tree α) (s : List α) :
  inorder' (mir t) s = rcat (inorder' t []) s := by
  induction t generalizing s with
  | ext => calc
      inorder' (mir .ext) s
      _ = inorder' .ext s           := at [1,1] use mir.ext
      _ = s                         := inorder'.ext s
      _ = rcat [] s                 := at [2] use rcat.nil s
      _ = rcat (inorder' .ext []) s := at [2,1] use inorder'.ext []
  | int x t1 t2 ih1 ih2 =>
      -- ih1 : inorder' (mir t1) s = rcat (inorder' t1 []) s
      -- ih2 : inorder' (mir t2) s = rcat (inorder' t2 []) s
      -- ⊢ inorder' (mir (Tree.int x t1 t2)) s = rcat (inorder' (Tree.int x t1 t2) []) s
      let mt1 := mir t1
      let mt2 := mir t2
      calc
      inorder' (mir (.int x t1 t2)) s
        = inorder' (.int x mt2 mt1) s                          := at [1,1] use mir.int x t1 t2
      _ = inorder' mt2 (x :: inorder' mt1 s)                   := inorder'.int s x mt2 mt1
      _ = inorder' mt2 (x :: rcat (inorder' t1 []) s)          := at [1,2,2] use ih1 s
      _ = rcat (inorder' t2 []) (x :: rcat (inorder' t1 []) s) := ih2 (x :: rcat (inorder' t1 []) s)
      _ = rcat (x :: inorder' t2 []) (rcat (inorder' t1 []) s) := at [2] use rcat.cons x _ _
      _ = rcat (cat (inorder' t1 []) (x :: inorder' t2 [])) s  := Rcat _ _ _
      _ = rcat (inorder' t1 (x :: inorder' t2 [])) s           := at [1,1] use CatIn _ _
      _ = rcat (inorder' (.int x t1 t2) []) s                  := at [2,1] use inorder'.int [] x _ _

theorem InMir {α : Type} (t : Tree α) :
  inorder (mir t) = rev (inorder t) := by
  calc
    inorder (mir t)
      = inorder' (mir t) []  := inorder.def (mir t)
    _ = rcat (inorder' t []) [] := InMir' t []
    _ = rev  (inorder' t [])    := at [2] use rev.def (inorder' t [])
    _ = rev (inorder t)         := at [2,1] use inorder.def t

-- theorem InMir {α : Type} (t : Tree α) :
--   inorder (mir t) = rev (inorder t) := by
--   induction t with
--   | ext => calc
--       inorder (mir .ext)
--         = inorder .ext           := at [1,1] use mir.ext
--       _ = inorder' .ext []       := inorder.def .ext
--       _ = []                     := inorder'.ext []
--       _ = rcat [] []             := at [2] use rcat.nil []
--       _ = rev []                 := at [2] use rev.def []
--       _ = rev (inorder' .ext []) := at [2,1] use inorder'.ext []
--       _ = rev (inorder .ext)     := at [2,1] use inorder.def .ext
--   | int x t1 t2 ih1 ih2 =>
--       -- ih1 : inorder (mir t1) = rev (inorder t1)
--       -- ih2 : inorder (mir t2) = rev (inorder t2)
--       -- ⊢ inorder (mir (.int x t1 t2)) = rev (inorder (.int x t1 t2))
--       let mt1 := mir t1
--       let mt2 := mir t2
--       calc
--       inorder (mir (.int x t1 t2))
--         = inorder (.int x mt2 mt1)             := at [1,1] use mir.int x t1 t2
--       _ = inorder' (.int x mt2 mt1) []         := inorder.def (.int x mt2 mt1)
--       _ = inorder' mt2 (x :: inorder' mt1 [])  := inorder'.int [] x mt2 mt1
--       _ = inorder' mt2 (x :: inorder mt1)      := at [2,2,2] use inorder.def mt1
--       _ = inorder' mt2 (x :: rev (inorder t1)) := at [1,2,2] use ih1
--       _ = rev (inorder (.int x t1 t2))         := by sorry


-- Postorder (a.k.a. postfix) traversals

def post' {α : Type} (t : Tree α) (s : List α) : List α :=
  match t with
  | .ext => s
  | .int x t1 t2 => post' t1 (post' t2 (x :: s))

theorem post'.ext {α : Type} : post' .ext s = s := rfl

theorem post'.int {α : Type} (x : α) (t1 t2 : Tree α) :
  post' (.int x t1 t2) s = post' t1 (post' t2 (x :: s)) := rfl

def post {α : Type} (t : Tree α) : List α := post' t []

theorem post.def {α : Type} (t : Tree α) : post t = post' t [] := rfl

attribute [irreducible] post' post

theorem PreMir' {α : Type} (t : Tree α) (s : List α) :
  pre' (mir t) s = rcat (post' t []) s := sorry


end BTree
