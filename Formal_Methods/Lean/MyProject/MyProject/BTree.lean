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

lemma pre.ext {α : Type} (s : List α) : pre.f .ext s = s := rfl

lemma pre.int {α : Type} (s : List α) (x : α) (t1 t2 : Tree α) :
  pre.f (.int x t1 t2) s = x :: pre.f t1 (pre.f t2 s) := rfl

lemma pre.def {α : Type} (t : Tree α) : pre t = pre.f t [] := rfl

attribute [irreducible] pre pre.f

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

/-! Involution of mirroring -/
theorem InvMir {α : Type} (t : Tree α) : mir (mir t) = t := by
  induction t with
  | ext =>
      calc
        mir (mir .ext)
          = mir .ext := at [1,1] use mir.ext
        _ = .ext     := mir.ext
  | int x t1 t2 ih1 ih2 =>
      guard_hyp ih1 : mir (mir t1) = t1
      guard_hyp ih2 : mir (mir t2) = t2
      show mir (mir (.int x t1 t2)) = .int x t1 t2
      calc
        mir (mir (.int x t1 t2))
          = mir (.int x (mir t2) (mir t1))       := at [1,1] use mir.int x t1 t2
        _ = .int x (mir (mir t1)) (mir (mir t2)) := mir.int x _ _
        _ = .int x t1 (mir (mir t2))             := at [1,2] use ih1
        _ = .int x t1 t2                         := at [1,3] use ih2

-- Inorder traversal

def «in» {α : Type} (t : Tree α) : List α := f t []
where
  f {α : Type} : Tree α -> List α -> List α
  | .ext,         s => s
  | .int x t1 t2, s => f t1 (x :: f t2 s)

lemma «in».ext {α : Type} (s : List α) : «in».f .ext s = s := rfl

lemma «in».int {α : Type} (s : List α) (x : α) (t1 t2 : Tree α) :
  «in».f (.int x t1 t2) s = «in».f t1 (x :: «in».f t2 s) := rfl

lemma «in».def {α : Type} (t : Tree α) :
  «in» t = «in».f t [] := rfl

attribute [irreducible] «in» «in».f

set_option linter.style.longLine false
lemma CatIn {α : Type} (t : Tree α) (s : List α) :
  cat («in».f t []) s = «in».f t s := by
  induction t generalizing s with
  | ext => calc
      cat («in».f .ext []) s
        = cat [] s        := at [1,1] use «in».ext []
      _ = s               := cat.nil s
      _ = «in».f .ext s   := at [2] use «in».ext s
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

lemma post.ext {α : Type} (s : List α) :
  post.f (.ext : Tree α) s = s := rfl

lemma post.int {α : Type} (x : α) (t1 t2 : Tree α) (s : List α) :
  post.f (.int x t1 t2) s = post.f t1 (post.f t2 (x :: s)) := rfl

lemma post.def {α : Type} (t : Tree α) : post t = post.f t [] := rfl

attribute [irreducible] post post.f

lemma CatPostGen {α : Type} (t : Tree α) (s1 s2 : List α) :
  cat (post.f t s1) s2 = post.f t (cat s1 s2) := by
  induction t generalizing s1 with
  | ext => calc
      cat (post.f .ext s1) s2
        = cat s1 s2               := at [1,1] use post.ext s1
      _ = post.f .ext (cat s1 s2) := at [2] use post.ext _
  | int x t1 t2 ih1 ih2 =>
      guard_hyp ih1 : ∀ (s1 : List α), cat (post.f t1 s1) s2 = post.f t1 (cat s1 s2)
      guard_hyp ih2 : ∀ (s1 : List α), cat (post.f t2 s1) s2 = post.f t2 (cat s1 s2)
      show cat (post.f (.int x t1 t2) s1) s2 = post.f (.int x t1 t2) (cat s1 s2)
      calc
        cat (post.f (.int x t1 t2) s1) s2
          = cat (post.f t1 (post.f t2 (x :: s1))) s2 := at [1,1] use post.int x t1 t2 s1
        _ = post.f t1 (cat (post.f t2 (x :: s1)) s2) := ih1 (post.f t2 (x :: s1))
        _ = post.f t1 (post.f t2 (cat (x :: s1) s2)) := at [1,2] use ih2 (x :: s1)
        _ = post.f t1 (post.f t2 (x :: cat s1 s2))   := at [1,2,2] use cat.cons _ _ _
        _ = post.f (.int x t1 t2) (cat s1 s2)        := at [2] use post.int x t1 t2 _

lemma CatPost {α : Type} (t : Tree α) (s : List α) :
  cat (post.f t []) s = post.f t s  := by
  calc
    cat (post.f t []) s
      = post.f t (cat [] s) := CatPostGen t [] s
    _ = post.f t s          := at [1,2] use cat.nil s

lemma PreMirGen {α : Type} (t : Tree α) (s : List α) :
  pre.f (mir t) s = rcat (post.f t []) s := by
  induction t generalizing s with
  | ext => calc
      pre.f (mir .ext) s
        = pre.f .ext s            := at [1,1] use mir.ext
      _ = s                       := pre.ext s
      _ = rcat [] s               := at [2] use rcat.nil s
      _ = rcat (post.f .ext []) s := at [2,1] use post.ext []
  | int x t1 t2 ih1 ih2 =>
      let mt1 : Tree α := mir t1
      let mt2 : Tree α := mir t2
      guard_hyp ih1 : ∀ (s : List α), pre.f mt1 s = rcat (post.f t1 []) s
      guard_hyp ih2 : ∀ (s : List α), pre.f mt2 s = rcat (post.f t2 []) s
      show pre.f (mir (.int x t1 t2)) s = rcat (post.f (.int x t1 t2) []) s
      calc
        pre.f (mir (.int x t1 t2)) s
          = pre.f (.int x mt2 mt1) s                                  := at [1,1] use mir.int _ _ _
        _ = x :: pre.f mt2 (pre.f mt1 s)                              := pre.int s x mt2 mt1
        _ = x :: pre.f mt2 (rcat (post.f t1 []) s)                    := at [1,2,2] use ih1 s
        _ = x :: rcat (post.f t2 []) (rcat (post.f t1 []) s)          := at [1,2] use ih2 _
        _ = x :: rcat (cat (post.f t1 []) (post.f t2 [])) s           := at [1,2] use Rcat _ _ _
        _ = rcat [] (x :: rcat (cat (post.f t1 []) (post.f t2 [])) s) := at [2] use rcat.nil _
        _ = rcat [x] (rcat (cat (post.f t1 []) (post.f t2 [])) s)     := at [2] use rcat.cons x [] _
        _ = rcat (cat (cat (post.f t1 []) (post.f t2 [])) [x]) s      := Rcat [x] _ s
        _ = rcat (cat (post.f t1 []) (cat (post.f t2 []) [x])) s      := at [2,1] use CatAssoc _ _ _
        _ = rcat (post.f t1 (cat (post.f t2 []) [x])) s               := at [1,1] use CatPost t1 _
        _ = rcat (post.f t1 (post.f t2 [x])) s                        := at [1,1,2] use CatPost t2 _
        _ = rcat (post.f (.int x t1 t2) []) s                         := at [2,1] use post.int x t1 t2 []

theorem PreMir {α : Type} (t : Tree α) :
  pre (mir t) = rev (post t) := by
  calc
    pre (mir t)
      = pre.f (mir t) []      := pre.def (mir t)
    _ = rcat (post.f t []) [] := PreMirGen t []
    _ = rcat (post t) []      := at [2,1] use post.def t
    _ = rev (post t)          := at [2] use rev.def (post t)

theorem PostMir {α : Type} (t : Tree α) :
  post (mir t) = rev (pre t) := by
  calc
    post (mir t)
      = rev (rev (post (mir t))) := at [2] use InvRev (post (mir t))
    _ = rev (pre (mir (mir t)))  := at [2,1] use PreMir (mir t)
    _ = rev (pre t)              := at [1,1,1] use InvMir t

/-! Postorder encoding (compare with `post`) -/
def epost {α : Type} (t : Tree α) : List (Option α) := f t []
where
  f {α : Type} : Tree α -> List (Option α) -> List (Option α)
  | .ext, s         => none :: s
  | .int x t1 t2, s => f t1 (f t2 (some x :: s))

lemma epost.ext {α : Type} (s : List (Option α)) :
  epost.f .ext s = none :: s := rfl

lemma epost.int {α : Type} (x : α) (t1 t2 : Tree α) (s : List (Option α)) :
  epost.f (.int x t1 t2) s = epost.f t1 (epost.f t2 (some x :: s)) := rfl

lemma epost.def {α : Type} (t : Tree α) : epost t = epost.f t [] := rfl

attribute [irreducible] epost epost.f

/-! Postorder decoding -/
def post2b {α : Type} (s : List (Option α)) : Option (Tree α) := f [] s
where
  f {α : Type} : List (Tree α) -> List (Option α) -> Option (Tree α)
  | [tree], []                      => some tree
  | forest, none :: s               => f (.ext :: forest) s
  | t2 :: t1 :: forest, some x :: s => f (.int x t1 t2 :: forest) s
  | _, _                            => none

lemma post2b.nil {α : Type} (t : Tree α) : post2b.f [t] [] = some t := rfl

lemma post2b.none {α : Type} (forest : List (Tree α)) (s : List (Option α)) :
  post2b.f forest (Option.none :: s) = post2b.f (.ext :: forest) s := by rw [post2b.f]

lemma post2b.some {α : Type} (t1 t2 : Tree α) (forest : List (Tree α)) (x : α) (s : List (Option α)) :
  post2b.f (t2 :: t1 :: forest) (Option.some x :: s) = post2b.f (.int x t1 t2 :: forest) s := rfl

lemma post2b.def {α : Type} (s : List (Option α)) : post2b s = post2b.f [] s := rfl

attribute [irreducible] post2b post2b.f

/-! Correctness of postorder encoding -/

theorem PostEnc {α : Type} (t : Tree α) : post2b (epost t) = some t := by
  induction t with
  | ext => calc
      post2b (epost .ext)
        = post2b (epost.f .ext []) := at [1,1] use epost.def .ext
      _ = post2b [none]            := at [1,1] use epost.ext []
      _ = post2b.f [] [none]       := post2b.def [none]
      _ = post2b.f [.ext] []       := post2b.none [] []
      _ = some .ext                := post2b.nil .ext
  | int x t1 t2 ih1 ih2 =>
     guard_hyp ih1 : post2b (epost t1) = some t1
     guard_hyp ih2 : post2b (epost t2) = some t2
     show post2b (epost (.int x t1 t2)) = some (.int x t1 t2)
     calc
       post2b (epost (.int x t1 t2))
         = post2b (epost.f (.int x t1 t2) []) := at [1,1] use epost.def _
       _ = post2b (epost.f t1 (epost.f t2 [some x])) := at [1,1] use epost.int _ _ _ []
       _ =  some (.int x t1 t2) := sorry

end BTree
