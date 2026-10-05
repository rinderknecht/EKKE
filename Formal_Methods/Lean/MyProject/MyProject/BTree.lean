import MyProject.MyList

/-! Our lists -/
open MyList

/-! Binary trees -/
namespace BTree

inductive Tree (α : Type) where
| ext
| int (x : α) (left right : Tree α)

-- Prefix traversals

/- Worst case quadratic cost -/
def pre0 {α : Type} : Tree α -> List α
| .ext         => []
| .int x t1 t2 => x :: cat (pre0 t1) (pre0 t2)

theorem pre0.ext {α : Type} : pre0 (Tree.ext : Tree α) = [] := rfl

theorem pre0.int {α : Type} (x : α) (t1 t2 : Tree α) :
  pre0 (Tree.int x t1 t2) = x :: cat (pre0 t1) (pre0 t2) := rfl

/- Worst case linear cost -/
def pre' {α : Type} (s : List α) : Tree α -> List α
| .ext         => s
| .int x t1 t2 => x :: pre' (pre' s t2) t1

theorem pre'.ext {α : Type} (s : List α) : pre' s Tree.ext = s := rfl

theorem pre'.int {α : Type} (s : List α) (x : α) (t1 t2 : Tree α) :
  pre' s (Tree.int x t1 t2) = x :: pre' (pre' s t2) t1 := rfl

def pre {α : Type} (t : Tree α) : List α := pre' [] t

lemma PreCat {α : Type} (t : Tree α) (s : List α) :
  cat (pre' [] t) s = pre' s t :=
  by induction t generalizing s with
  | ext => calc
      cat (pre' [] Tree.ext) s
        = cat [] s             := by conv => lhs; rw [pre'.ext]
      _ = s                    := by conv => lhs; rw [cat.nil]
      _ = pre' s Tree.ext      := by conv => rhs; rw [pre'.ext]
  | int x t1 t2 ih1 ih2 => calc
     cat (pre' [] (Tree.int x t1 t2)) s
       = cat (x :: pre' (pre' [] t2) t1) s          := by conv => lhs; rw [pre'.int]
     _ = x :: cat (pre' (pre' [] t2) t1) s          := by conv => lhs; rw [cat.cons]
     _ = x :: cat (cat (pre' [] t1) (pre' [] t2)) s := by conv => rhs; rw [ih1]
     _ = x :: cat (pre' [] t1) (cat (pre' [] t2) s) := by conv => rhs; rw [CatAssoc]
     _ = x :: cat (pre' [] t1) (pre' s t2)          := by conv => lhs; rw [ih2]
     _ = x :: pre' (pre' s t2) t1                   := by conv => lhs; rw [ih1]
     _ = pre' s (Tree.int x t1 t2)                  := by conv => rhs; rw [pre'.int]

/-! The two preorder traversals are equivalent -/
theorem PreEquiv {α : Type} (t : Tree α) : pre0 t = pre t :=
  by induction t with
  | ext => calc
      pre0 Tree.ext
        = []               := by conv => lhs; rw [pre0.ext]
      _ = pre' [] Tree.ext := by conv => rhs; rw [pre'.ext]
      _ = pre Tree.ext     := by conv => rhs; rw [pre]
  | int x t1 t2 h1 h2 => calc
      pre0 (Tree.int x t1 t2)
        = x :: cat (pre0 t1) (pre0 t2)       := by conv => lhs; rw [pre0.int]
      _ = x :: cat (pre t1) (pre t2)         := by conv => lhs; rw [h1, h2]
      _ = x :: cat (pre' [] t1) (pre' [] t2) := by conv => lhs; rw [pre, pre]
      _ = x :: pre' (pre' [] t2) t1          := by conv => lhs; rw [PreCat]
      _ = pre' [] (Tree.int x t1 t2)         := by conv => rhs; rw [pre'.int]
      _ = pre (Tree.int x t1 t2)             := by conv => rhs; rw [pre]

-- Mirroring

def mirror {α : Type} : Tree α -> Tree α
| .ext => .ext
| .int x t1 t2 => Tree.int x (mirror t2) (mirror t1)

theorem mirror.ext {α : Type} : mirror (Tree.ext : Tree α) = Tree.ext := rfl

theorem mirror.int {α : Type} (x : α) (t1 t2 : Tree α) :
  mirror (Tree.int x t1 t2) = Tree.int x (mirror t2) (mirror t1) := rfl

-- Inorder traversal

def inorder' {α : Type} (s : List α) : Tree α -> List α
| .ext         => s
| .int x t1 t2 => inorder' (x :: inorder' s t2) t1

theorem inorder'.ext {α : Type} (s : List α) : inorder' s (Tree.ext) = s := rfl

theorem inorder'.int {α : Type} (s : List α) (x : α) (t1 t2 : Tree α) :
  inorder' s (Tree.int x t1 t2) = inorder' (x :: inorder' s t2) t1 := rfl

def inorder {α : Type} (t : Tree α) : List α := inorder' [] t

theorem InMir {α : Type} (t : Tree α) :
  inorder (mirror t) = rev (inorder t) :=
  by induction t with
  | ext => calc
      inorder (mirror Tree.ext)
        = inorder Tree.ext           := by conv => lhs; rw [mirror.ext]
      _ = inorder' [] Tree.ext       := by conv => lhs; rw [inorder]
      _ = []                         := by conv => lhs; rw [inorder'.ext]
      _ = rcat [] []                 := by conv => rhs; rw [rcat.nil]
      _ = rev []                     := by conv => rhs; rw [rev]
      _ = rev (inorder' [] Tree.ext) := by conv => rhs; rw [inorder'.ext]
      _ = rev (inorder Tree.ext)     := by conv => rhs; rw [inorder]
  | int x t1 t2 ih1 ih2 => sorry

end BTree
