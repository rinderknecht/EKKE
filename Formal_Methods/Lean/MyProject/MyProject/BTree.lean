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

/- Worst case linear cost -/
def pre' {α : Type} (s : List α) : Tree α -> List α
| .ext         => s
| .int x t1 t2 => x :: pre' (pre' s t2) t1

def pre {α : Type} (t : Tree α) : List α := pre' [] t

lemma PreCat {α : Type} (t : Tree α) (s : List α) :
  cat (pre' [] t) s = pre' s t :=
  by induction t generalizing s with
  | ext => calc
      cat (pre' [] Tree.ext) s
        = cat [] s             := rfl -- -> pre'|1
      _ = s                    := rfl -- -> cat| 1
      _ = pre' s Tree.ext      := rfl -- <- pre'|1
  | int x t1 t2 ih1 ih2 => calc
     cat (pre' [] (Tree.int x t1 t2)) s
       = cat (x :: pre' (pre' [] t2) t1) s          := rfl -- -> pre'|1
     _ = x :: cat (pre' (pre' [] t2) t1) s          := rfl -- <- cat|2
     _ = x :: cat (cat (pre' [] t1) (pre' [] t2)) s := by rw [<- ih1]
     _ = x :: cat (pre' [] t1) (cat (pre' [] t2) s) := by rw [<- CatAssoc]
     _ = x :: cat (pre' [] t1) (pre' s t2)          := by rw [ih2]
     _ = x :: pre' (pre' s t2) t1                   := by rw [ih1]
     _ = pre' s (Tree.int x t1 t2)                  := rfl -- <- pre'|2

/-! The two preorder traversals are equivalent -/
theorem PreEquiv {α : Type} (t : Tree α) : pre0 t = pre t :=
  by induction t with
  | ext => calc
      pre0 Tree.ext
        = []               := rfl -- -> pre0|1
      _ = pre' [] Tree.ext := rfl -- <- pre'|1
      _ = pre Tree.ext     := rfl -- -> pre
  | int x t1 t2 h1 h2 => calc
      pre0 (Tree.int x t1 t2)
        = x :: cat (pre0 t1) (pre0 t2)       := rfl            -- -> pre0|2
      _ = x :: cat (pre t1) (pre t2)         := by rw [h1, h2]
      _ = x :: cat (pre' [] t1) (pre' [] t2) := rfl            -- -2-> pre
      _ = x :: pre' (pre' [] t2) t1          := by rw [PreCat]
      _ = pre' [] (Tree.int x t1 t2)         := rfl            -- <- pre'|2
      _ = pre (Tree.int x t1 t2)             := rfl            -- <- pre

-- Mirroring

def mirror {α : Type} : Tree α -> Tree α
| .ext => .ext
| .int x t1 t2 => Tree.int x (mirror t2) (mirror t1)

-- Inorder traversal

def inorder' {α : Type} (s : List α) : Tree α -> List α
| .ext         => s
| .int x t1 t2 => inorder' (x :: inorder' s t2) t1

def inorder {α : Type} (t : Tree α) : List α := inorder' [] t

theorem InMir {α : Type} (t : Tree α) :
  inorder (mirror t) = rev (inorder t) :=
  sorry

n
end BTree
