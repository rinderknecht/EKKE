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

/-! Worst case has quadratic cost -/
def pre0 {α : Type} : Tree α -> List α
| .ext         => []
| .int x t1 t2 => x :: cat (pre0 t1) (pre0 t2)

theorem pre0.ext {α : Type} : pre0 (.ext : Tree α) = [] := rfl

theorem pre0.int {α : Type} (x : α) (t1 t2 : Tree α) :
  pre0 (.int x t1 t2) = x :: cat (pre0 t1) (pre0 t2) := rfl

attribute [irreducible] pre0

/-! Worst case has linear cost -/
def pre {α : Type} (t : Tree α) : List α := f t []
where
  f {α : Type} : Tree α -> List α -> List α
  | .ext,         s => s
  | .int x t1 t2, s => x :: f t1 (f t2 s)

theorem pre.ext {α : Type} (s : List α) : pre.f .ext s = s := rfl

theorem pre.int {α : Type} (s : List α) (x : α) (t1 t2 : Tree α) :
  pre.f (.int x t1 t2) s = x :: pre.f t1 (pre.f t2 s) := rfl

theorem pre.def {α : Type} (t : Tree α) : pre t = pre.f t [] := rfl

attribute [irreducible] pre

lemma CatPre {α : Type} (t : Tree α) (s : List α) :
  cat (pre.f t []) s = pre.f t s := by
  induction t generalizing s with
  | ext => calc
      cat (pre.f .ext []) s
        = cat [] s         := at [1,1] use pre.ext []
      _ = s                := cat.nil s
      _ = pre.f .ext s     := at [2] use pre.ext s
  | int x t1 t2 ih1 ih2 =>
      guard_hyp ih1 : ∀ (s : List α), cat (pre.f t1 []) s = pre.f t1 s
      guard_hyp ih2 : ∀ (s : List α), cat (pre.f t2 []) s = pre.f t2 s
      show cat (pre.f (.int x t1 t2) []) s = pre.f (.int x t1 t2) s
      calc
        cat (pre.f (.int x t1 t2) []) s
          = cat (x :: pre.f t1 (pre.f t2 [])) s          := at [1,1] use pre.int [] x t1 t2
        _ = x :: cat (pre.f t1 (pre.f t2 [])) s          := cat.cons x (pre.f t1 (pre.f t2 [])) s
        _ = x :: cat (cat (pre.f t1 []) (pre.f t2 [])) s := at [2,2,1] use ih1 (pre.f t2 [])
        _ = x :: cat (pre.f t1 []) (cat (pre.f t2 []) s) := at [2,2] use CatAssoc _ _ s
        _ = x :: cat (pre.f t1 []) (pre.f t2 s)          := at [1,2,2] use ih2 s
        _ = x :: pre.f t1 (pre.f t2 s)                   := at [1,2] use ih1 (pre.f t2 s)
        _ = pre.f (.int x t1 t2) s                       := at [2] use pre.int s x t1 t2

/-! The two preorder traversals are equivalent -/
theorem Pre {α : Type} (t : Tree α) : pre0 t = pre t := by
  induction t with
  | ext => calc
      pre0 .ext
        = []            := pre0.ext
      _ = pre.f .ext [] := at [2] use pre.ext []
      _ = pre .ext      := at [2] use pre.def .ext
  | int x t1 t2 h1 h2 =>
      guard_hyp h1 : pre0 t1 = pre t1
      guard_hyp h2 : pre0 t2 = pre t2
      show pre0 (Tree.int x t1 t2) = pre (Tree.int x t1 t2)
      calc
        pre0 (.int x t1 t2)
          = x :: cat (pre0 t1) (pre0 t2)         := pre0.int x t1 t2
        _ = x :: cat (pre t1) (pre0 t2)          := at [1,2,1] use h1
        _ = x :: cat (pre t1) (pre t2)           := at [1,2,2] use h2
        _ = x :: cat (pre.f t1 []) (pre t2)      := at [1,2,1] use pre.def t1
        _ = x :: cat (pre.f t1 []) (pre.f t2 []) := at [1,2,2] use pre.def t2
        _ = x :: pre.f t1 (pre.f t2 [])          := at [1,2] use CatPre t1 (pre.f t2 [])
        _ = pre.f (.int x t1 t2) []              := at [2] use pre.int [] x t1 t2
        _ = pre (.int x t1 t2)                   := at [2] use pre.def (.int x t1 t2)

-- Mirroring

def mir {α : Type} : Tree α -> Tree α
| .ext         => .ext
| .int x t1 t2 => .int x (mir t2) (mir t1)

theorem mir.ext {α : Type} : mir (.ext : Tree α) = .ext := rfl

theorem mir.int {α : Type} (x : α) (t1 t2 : Tree α) :
  mir (.int x t1 t2) = .int x (mir t2) (mir t1) := rfl

attribute [irreducible] mir

-- Inorder traversal

def «in» {α : Type} (t : Tree α) : List α := f t []
where
  f {α : Type} : Tree α -> List α -> List α
  | .ext,         s => s
  | .int x t1 t2, s => f t1 (x :: f t2 s)

theorem «in».ext {α : Type} (s : List α) : «in».f .ext s = s := rfl

theorem «in».int {α : Type} (s : List α) (x : α) (t1 t2 : Tree α) :
  «in».f (.int x t1 t2) s = «in».f t1 (x :: «in».f t2 s) := rfl

theorem «in».def {α : Type} (t : Tree α) :
  «in» t = «in».f t [] := rfl

attribute [irreducible] «in»

set_option linter.style.longLine false
lemma CatIn {α : Type} (t : Tree α) (s : List α) :
  cat («in».f t []) s = «in».f t s := by
  induction t generalizing s with
  | ext => calc
      cat («in».f .ext []) s
        = cat [] s        := at [1,1] use «in».ext []
      _ = s               := cat.nil s
      _ = «in».f .ext s := at [2] use «in».ext s
  | int x t1 t2 ih1 ih2 =>
      guard_hyp ih1 : ∀ (s : List α), cat («in».f t1 []) s = «in».f t1 s
      guard_hyp ih2 : ∀ (s : List α), cat («in».f t2 []) s = «in».f t2 s
      show cat («in».f (.int x t1 t2) []) s = «in».f (.int x t1 t2) s
      calc
        cat («in».f (.int x t1 t2) []) s
          = cat («in».f t1 (x :: «in».f t2 [])) s          := at [1,1] use «in».int [] x t1 t2
        _ = cat (cat («in».f t1 []) (x :: «in».f t2 [])) s := at [2,1] use ih1 (x :: «in».f t2 [])
        _ = cat («in».f t1 []) (cat (x :: «in».f t2 []) s) := at [2] use CatAssoc _ _ s
        _ = cat («in».f t1 []) (x :: cat («in».f t2 []) s) := at [1,2] use cat.cons x _ s
        _ = cat («in».f t1 []) (x :: «in».f t2 s)          := at [1,2,2] use ih2 s
        _ = «in».f t1 (x :: «in».f t2 s)                   := ih1 (x :: «in».f t2 s)
        _ = «in».f (.int x t1 t2) s                        := at [2] use «in».int s x t1 t2

set_option linter.style.show false
lemma InMir' {α : Type} (t : Tree α) (s : List α) :
  «in».f (mir t) s = rcat («in».f t []) s := by
  induction t generalizing s with
  | ext => calc
      «in».f (mir .ext) s
      _ = «in».f .ext s           := at [1,1] use mir.ext
      _ = s                       := «in».ext s
      _ = rcat [] s               := at [2] use rcat.nil s
      _ = rcat («in».f .ext []) s := at [2,1] use «in».ext []
  | int x t1 t2 ih1 ih2 =>
      let mt1 : Tree α := mir t1
      let mt2 : Tree α := mir t2
      guard_hyp ih1 : ∀ (s : List α), «in».f mt1 s = rcat («in».f t1 []) s
      guard_hyp ih2 : ∀ (s : List α), «in».f mt2 s = rcat («in».f t2 []) s
      show «in».f (mir (Tree.int x t1 t2)) s = rcat («in».f (Tree.int x t1 t2) []) s
      calc
        «in».f (mir (.int x t1 t2)) s
          = «in».f (.int x mt2 mt1) s                        := at [1,1] use mir.int x t1 t2
        _ = «in».f mt2 (x :: «in».f mt1 s)                   := «in».int s x mt2 mt1
        _ = «in».f mt2 (x :: rcat («in».f t1 []) s)          := at [1,2,2] use ih1 s
        _ = rcat («in».f t2 []) (x :: rcat («in».f t1 []) s) := ih2 (x :: rcat («in».f t1 []) s)
        _ = rcat (x :: «in».f t2 []) (rcat («in».f t1 []) s) := at [2] use rcat.cons x _ _
        _ = rcat (cat («in».f t1 []) (x :: «in».f t2 [])) s  := Rcat _ _ _
        _ = rcat («in».f t1 (x :: «in».f t2 [])) s           := at [1,1] use CatIn _ _
        _ = rcat («in».f (.int x t1 t2) []) s                := at [2,1] use «in».int [] x _ _

theorem InMir {α : Type} (t : Tree α) :
  «in» (mir t) = rev («in» t) := by
  calc
    «in» (mir t)
      = «in».f (mir t) []     := «in».def (mir t)
    _ = rcat («in».f t []) [] := InMir' t []
    _ = rev  («in».f t [])    := at [2] use rev.def («in».f t [])
    _ = rev («in» t)          := at [2,1] use «in».def t

-- Postorder (a.k.a. postfix) traversals

def post {α : Type} (t : Tree α) : List α := f t []
where
  f {α : Type} : Tree α -> List α -> List α
  | .ext,         s => s
  | .int x t1 t2, s => f t1 (f t2 (x :: s))

theorem post.ext {α : Type} (s : List α) :
  post.f (.ext : Tree α) s = s := rfl

theorem post.int {α : Type} (x : α) (t1 t2 : Tree α) (s : List α) :
  post.f (.int x t1 t2) s = post.f t1 (post.f t2 (x :: s)) := rfl

theorem post.def {α : Type} (t : Tree α) : post t = post.f t [] := rfl

attribute [irreducible] post

theorem PreMir {α : Type} (t : Tree α) (s : List α) :
  pre.f (mir t) s = rcat (post.f t []) s := sorry


end BTree
