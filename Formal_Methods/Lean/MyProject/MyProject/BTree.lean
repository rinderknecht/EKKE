import MyProject.MyList -- Imports transitively `Mathlib.Order.Basic`

/-! Binary trees -/
namespace BTree


/-! Our lists -/
open MyList

inductive Tree (α : Type) where
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
def pre' {α : Type} (s : List α) : Tree α -> List α
| .ext         => s
| .int x t1 t2 => x :: pre' (pre' s t2) t1

theorem pre'.ext {α : Type} (s : List α) : pre' s .ext = s := rfl

theorem pre'.int {α : Type} (s : List α) (x : α) (t1 t2 : Tree α) :
  pre' s (.int x t1 t2) = x :: pre' (pre' s t2) t1 := rfl

def pre {α : Type} (t : Tree α) : List α := pre' [] t

theorem pre.def {α : Type} (t : Tree α) : pre t = pre' [] t := rfl

attribute [irreducible] pre' pre

lemma PreCat {α : Type} (t : Tree α) (s : List α) :
  cat (pre' [] t) s = pre' s t := by
  induction t generalizing s with
  | ext => calc
      cat (pre' [] .ext) s
        = cat [] s         := at [1,1] use pre'.ext []
      _ = s                := cat.nil s
      _ = pre' s .ext      := at [2] use pre'.ext s
  | int x t1 t2 ih1 ih2 => calc
      -- ih1 : ∀ (s : List α), cat (pre' [] t1) s = pre' s t1
      -- ih2 : ∀ (s : List α), cat (pre' [] t2) s = pre' s t2
      -- ⊢ cat (pre' [] (Tree.int x t1 t2)) s = pre' s (Tree.int x t1 t2)
     cat (pre' [] (.int x t1 t2)) s
       = cat (x :: pre' (pre' [] t2) t1) s          := at [1,1] use pre'.int [] x t1 t2
     _ = x :: cat (pre' (pre' [] t2) t1) s          := cat.cons x (pre' (pre' [] t2) t1) s
     _ = x :: cat (cat (pre' [] t1) (pre' [] t2)) s := at [2,2,1] use ih1 (pre' [] t2)
     _ = x :: cat (pre' [] t1) (cat (pre' [] t2) s) := at [2,2]
                                                       use CatAssoc (pre' [] t1) (pre' [] t2) s
     _ = x :: cat (pre' [] t1) (pre' s t2)          := at [1,2,2] use ih2 s
     _ = x :: pre' (pre' s t2) t1                   := at [1,2] use ih1 (pre' s t2)
     _ = pre' s (.int x t1 t2)                      := at [2] use pre'.int s x t1 t2

/-! The two preorder traversals are equivalent -/
theorem PreEquiv {α : Type} (t : Tree α) : pre0 t = pre t := by
  induction t with
  | ext => calc
      pre0 .ext
        = []           := pre0.ext
      _ = pre' [] .ext := at [2] use pre'.ext []
      _ = pre .ext     := at [2] use pre.def .ext
  | int x t1 t2 h1 h2 => calc
      pre0 (.int x t1 t2)
        = x :: cat (pre0 t1) (pre0 t2)       := pre0.int x t1 t2
      _ = x :: cat (pre t1) (pre0 t2)        := at [1,2,1] use h1
      _ = x :: cat (pre t1) (pre t2)         := at [1,2,2] use h2
      _ = x :: cat (pre' [] t1) (pre t2)     := at [1,2,1] use pre.def t1
      _ = x :: cat (pre' [] t1) (pre' [] t2) := at [1,2,2] use pre.def t2
      _ = x :: pre' (pre' [] t2) t1          := at [1,2] use PreCat t1 (pre' [] t2)
      _ = pre' [] (.int x t1 t2)             := at [2] use pre'.int [] x t1 t2
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

def inorder' {α : Type} (s : List α) : Tree α -> List α
| .ext         => s
| .int x t1 t2 => inorder' (x :: inorder' s t2) t1

theorem inorder'.ext {α : Type} (s : List α) : inorder' s (.ext) = s := rfl

theorem inorder'.int {α : Type} (s : List α) (x : α) (t1 t2 : Tree α) :
  inorder' s (.int x t1 t2) = inorder' (x :: inorder' s t2) t1 := rfl

def inorder {α : Type} (t : Tree α) : List α := inorder' [] t

theorem inorder.def {α : Type} (t : Tree α) : inorder t = inorder' [] t := rfl

attribute [irreducible] inorder

theorem InMir {α : Type} (t : Tree α) : inorder (mirror t) = rev (inorder t) := by
  induction t with
  | ext => calc
      inorder (mirror .ext)
        = inorder .ext           := at [1,1] use mirror.ext
      _ = inorder' [] .ext       := inorder.def .ext
      _ = []                     := inorder'.ext []
      _ = rcat [] []             := at [2] use rcat.nil []
      _ = rev []                 := at [2] use rev.def []
      _ = rev (inorder' [] .ext) := at [2,1] use inorder'.ext []
      _ = rev (inorder .ext)     := at [2,1] use inorder.def .ext
  | int x t1 t2 ih1 ih2 =>
     -- ih1 : inorder (mirror t1) = rev (inorder t1)
     -- ih2 : inorder (mirror t2) = rev (inorder t2)
     -- ⊢ inorder (mirror (.int x t1 t2)) = rev (inorder (.int x t1 t2))
      let mt1 := mirror t1
      let mt2 := mirror t2
      calc
      inorder (mirror (.int x t1 t2))
        = inorder (.int x mt2 mt1)            := at [1,1] use mirror.int x t1 t2
      _ = inorder' [] (.int x mt2 mt1)        := inorder.def (.int x mt2 mt1)
      _ = inorder' (x :: inorder' [] mt1) mt2 := inorder'.int [] x mt2 mt1
      _ = rev (inorder (.int x t1 t2))        := by sorry

end BTree
