import Mathlib.Order.Basic
import MyProject.MyList

/-! Our lists -/
open MyList

/-! Binary Search Trees -/
namespace BST

inductive Tree (α : Type) [LinearOrder α] : Type where
| ext                                  -- External node
| int (root : α) (left right : Tree α) -- Internal node

/-! Leaf insertion (with duplicates to the right) -/
def insl {α : Type} [LinearOrder α] (y : α) : Tree α -> Tree α
| .ext         => .int y .ext .ext -- new leaf (and root if empty tree)
| .int x t₁ t₂ => if x > y then .int x (insl y t₁) t₂ else .int x t₁ (insl y t₂)

/-! Inserting list items as leaves, from right to left -/
def mklR {α : Type} [LinearOrder α] : List α -> Tree α
| []     => .ext
| x :: s => insl x (mklR s)

/-! Right rotation (at the root) -/
def rotr {α : Type} [LinearOrder α] : Tree α -> Tree α
| .int y (.int x t₁ t₂) t₃ => .int x t₁ (.int y t₂ t₃)
| t => t

/-! Left rotation (at the root) -/
def rotl {α : Type} [LinearOrder α] : Tree α -> Tree α
| .int x t₁ (.int y t₂ t₃) => .int y (.int x t₁ t₂) t₃
| t => t

/-! Root insertion -/
def insr {α : Type} [LinearOrder α] (y : α) : Tree α -> Tree α
| .ext         => .int y .ext .ext
| .int x t₁ t₂ => if x > y then rotr (.int x (insr y t₁) t₂)
                  else rotl (.int x t₁ (insr y t₂))

/-! Inserting list items as roots, from left to right -/
def mkr {α : Type} [LinearOrder α] : List α -> Tree α -> Tree α
| [], t     => t
| x :: s, t => mkr s (insr x t)

def mkr.def {α : Type} [LinearOrder α] (s : List α) : Tree α := mkr s .ext

end BST
