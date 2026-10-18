import Mathlib.Order.Basic

import MyProject.MyList

/-! Our lists -/
open MyList

/-! Binary trees -/
namespace BTree

inductive Tree (α : Type) : Type where
| ext
| int (x : α) (left right : Tree α)

-- Prefix traversals

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
     _ = x :: cat (pre' t1 []) (cat (pre' t2 []) s) := at [2,2]
                                                       use CatAssoc (pre' t1 []) (pre' t2 []) s
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

def mirror {α : Type} : Tree α -> Tree α
| .ext => .ext
| .int x t1 t2 => .int x (mirror t2) (mirror t1)

theorem mirror.ext {α : Type} : mirror (.ext : Tree α) = .ext := rfl

theorem mirror.int {α : Type} (x : α) (t1 t2 : Tree α) :
  mirror (.int x t1 t2) = .int x (mirror t2) (mirror t1) := rfl

attribute [irreducible] mirror

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
      _ = cat (cat (inorder' t1 []) (x :: inorder' t2 [])) s := at [2,1]
                                                                use ih1 (x :: inorder' t2 [])
      _ = cat (inorder' t1 []) (cat (x :: inorder' t2 []) s) := at [2]
                                                                use CatAssoc (inorder' t1 [])
                                                                             (x :: inorder' t2 []) s
      _ = cat (inorder' t1 []) (x :: cat (inorder' t2 []) s) := at [1,2]
                                                                use cat.cons x (inorder' t2 []) s
      _ = cat (inorder' t1 []) (x :: inorder' t2 s)          := at [1,2,2] use ih2 s
      _ = inorder' t1 (x :: inorder' t2 s)                   := ih1 (x :: inorder' t2 s)
      _ = inorder' (.int x t1 t2) s                          := at [2] use inorder'.int s x t1 t2

theorem InMir {α : Type} (t : Tree α) :
  inorder (mirror t) = rev (inorder t) := by
  induction t with
  | ext => calc
      inorder (mirror .ext)
        = inorder .ext           := at [1,1] use mirror.ext
      _ = inorder' .ext []       := inorder.def .ext
      _ = []                     := inorder'.ext []
      _ = rcat [] []             := at [2] use rcat.nil []
      _ = rev []                 := at [2] use rev.def []
      _ = rev (inorder' .ext []) := at [2,1] use inorder'.ext []
      _ = rev (inorder .ext)     := at [2,1] use inorder.def .ext
  | int x t1 t2 ih1 ih2 =>
     -- ih1 : inorder (mirror t1) = rev (inorder t1)
     -- ih2 : inorder (mirror t2) = rev (inorder t2)
     -- ⊢ inorder (mirror (.int x t1 t2)) = rev (inorder (.int x t1 t2))
      let mt1 := mirror t1
      let mt2 := mirror t2
      calc
      inorder (mirror (.int x t1 t2))
        = inorder (.int x mt2 mt1)             := at [1,1] use mirror.int x t1 t2
      _ = inorder' (.int x mt2 mt1) []         := inorder.def (.int x mt2 mt1)
      _ = inorder' mt2 (x :: inorder' mt1 [])  := inorder'.int [] x mt2 mt1
      _ = inorder' mt2 (x :: inorder mt1)      := at [2,2,2] use inorder.def mt1
      _ = inorder' mt2 (x :: rev (inorder t1)) := at [1,2,2] use ih1
      _ = rev (inorder (.int x t1 t2))         := by sorry

end BTree
