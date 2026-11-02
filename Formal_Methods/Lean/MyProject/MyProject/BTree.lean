import Mathlib.Order.Basic

import MyProject.MyList

/-! Our lists -/
open MyList

/-! Binary trees -/
namespace BTree

inductive Tree (α : Type) : Type where
| ext                                  -- External node
| int (root : α) (left right : Tree α) -- Internal node

-- Preorder (a.k.a. prefix) traversals

/-! Worst case has quadratic cost -/
def pre0 {α : Type} : Tree α -> List α
| .ext         => []
| .int x t₁ t₂ => x :: cat (pre0 t₁) (pre0 t₂)

theorem pre0.ext {α : Type} : pre0 (.ext : Tree α) = [] := rfl

theorem pre0.int {α : Type} (x : α) (t₁ t₂ : Tree α) :
  pre0 (.int x t₁ t₂) = x :: cat (pre0 t₁) (pre0 t₂) := rfl

attribute [irreducible] pre0

/-! Worst case has linear cost -/
def pre {α : Type} (t : Tree α) : List α := f t []
where
  f {α : Type} : Tree α -> List α -> List α
  | .ext,         s => s
  | .int x t₁ t₂, s => x :: f t₁ (f t₂ s)

lemma pre.ext {α : Type} (s : List α) : pre.f .ext s = s := rfl

lemma pre.int {α : Type} (s : List α) (x : α) (t₁ t₂ : Tree α) :
  pre.f (.int x t₁ t₂) s = x :: pre.f t₁ (pre.f t₂ s) := rfl

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
  | int x t₁ t₂ ih₁ ih₂ =>
      guard_hyp ih₁ : ∀ (s : List α), cat (pre.f t₁ []) s = pre.f t₁ s
      guard_hyp ih₂ : ∀ (s : List α), cat (pre.f t₂ []) s = pre.f t₂ s
      show cat (pre.f (.int x t₁ t₂) []) s = pre.f (.int x t₁ t₂) s
      calc
        cat (pre.f (.int x t₁ t₂) []) s
          = cat (x :: pre.f t₁ (pre.f t₂ [])) s          := at [1,1] use pre.int [] x t₁ t₂
        _ = x :: cat (pre.f t₁ (pre.f t₂ [])) s          := cat.cons x (pre.f t₁ (pre.f t₂ [])) s
        _ = x :: cat (cat (pre.f t₁ []) (pre.f t₂ [])) s := at [2,2,1] use ih₁ (pre.f t₂ [])
        _ = x :: cat (pre.f t₁ []) (cat (pre.f t₂ []) s) := at [2,2] use CatAssoc _ _ s
        _ = x :: cat (pre.f t₁ []) (pre.f t₂ s)          := at [1,2,2] use ih₂ s
        _ = x :: pre.f t₁ (pre.f t₂ s)                   := at [1,2] use ih₁ (pre.f t₂ s)
        _ = pre.f (.int x t₁ t₂) s                       := at [2] use pre.int s x t₁ t₂

/-! The two preorder traversals are equivalent -/
theorem Pre {α : Type} (t : Tree α) : pre0 t = pre t := by
  induction t with
  | ext => calc
      pre0 .ext
        = []            := pre0.ext
      _ = pre.f .ext [] := at [2] use pre.ext []
      _ = pre .ext      := at [2] use pre.def .ext
  | int x t₁ t₂ h1 h2 =>
      guard_hyp h1 : pre0 t₁ = pre t₁
      guard_hyp h2 : pre0 t₂ = pre t₂
      show pre0 (Tree.int x t₁ t₂) = pre (Tree.int x t₁ t₂)
      calc
        pre0 (.int x t₁ t₂)
          = x :: cat (pre0 t₁) (pre0 t₂)         := pre0.int x t₁ t₂
        _ = x :: cat (pre t₁) (pre0 t₂)          := at [1,2,1] use h1
        _ = x :: cat (pre t₁) (pre t₂)           := at [1,2,2] use h2
        _ = x :: cat (pre.f t₁ []) (pre t₂)      := at [1,2,1] use pre.def t₁
        _ = x :: cat (pre.f t₁ []) (pre.f t₂ []) := at [1,2,2] use pre.def t₂
        _ = x :: pre.f t₁ (pre.f t₂ [])          := at [1,2] use CatPre t₁ (pre.f t₂ [])
        _ = pre.f (.int x t₁ t₂) []              := at [2] use pre.int [] x t₁ t₂
        _ = pre (.int x t₁ t₂)                   := at [2] use pre.def (.int x t₁ t₂)

-- Mirroring

def mir {α : Type} : Tree α -> Tree α
| .ext         => .ext
| .int x t₁ t₂ => .int x (mir t₂) (mir t₁)

theorem mir.ext {α : Type} : mir (.ext : Tree α) = .ext := rfl

theorem mir.int {α : Type} (x : α) (t₁ t₂ : Tree α) :
  mir (.int x t₁ t₂) = .int x (mir t₂) (mir t₁) := rfl

attribute [irreducible] mir

/-! Involution of mirroring -/
theorem InvMir {α : Type} (t : Tree α) : mir (mir t) = t := by
  induction t with
  | ext =>
      calc
        mir (mir .ext)
          = mir .ext := at [1,1] use mir.ext
        _ = .ext     := mir.ext
  | int x t₁ t₂ ih₁ ih₂ =>
      guard_hyp ih₁ : mir (mir t₁) = t₁
      guard_hyp ih₂ : mir (mir t₂) = t₂
      show mir (mir (.int x t₁ t₂)) = .int x t₁ t₂
      calc
        mir (mir (.int x t₁ t₂))
          = mir (.int x (mir t₂) (mir t₁))       := at [1,1] use mir.int x t₁ t₂
        _ = .int x (mir (mir t₁)) (mir (mir t₂)) := mir.int x _ _
        _ = .int x t₁ (mir (mir t₂))             := at [1,2] use ih₁
        _ = .int x t₁ t₂                         := at [1,3] use ih₂

-- Inorder traversal

def «in» {α : Type} (t : Tree α) : List α := f t []
where
  f {α : Type} : Tree α -> List α -> List α
  | .ext,         s => s
  | .int x t₁ t₂, s => f t₁ (x :: f t₂ s)

lemma «in».ext {α : Type} (s : List α) : «in».f .ext s = s := rfl

lemma «in».int {α : Type} (s : List α) (x : α) (t₁ t₂ : Tree α) :
  «in».f (.int x t₁ t₂) s = «in».f t₁ (x :: «in».f t₂ s) := rfl

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
  | int x t₁ t₂ ih₁ ih₂ =>
      guard_hyp ih₁ : ∀ (s : List α), cat («in».f t₁ []) s = «in».f t₁ s
      guard_hyp ih₂ : ∀ (s : List α), cat («in».f t₂ []) s = «in».f t₂ s
      show cat («in».f (.int x t₁ t₂) []) s = «in».f (.int x t₁ t₂) s
      calc
        cat («in».f (.int x t₁ t₂) []) s
          = cat («in».f t₁ (x :: «in».f t₂ [])) s          := at [1,1] use «in».int [] x t₁ t₂
        _ = cat (cat («in».f t₁ []) (x :: «in».f t₂ [])) s := at [2,1] use ih₁ (x :: «in».f t₂ [])
        _ = cat («in».f t₁ []) (cat (x :: «in».f t₂ []) s) := at [2] use CatAssoc _ _ s
        _ = cat («in».f t₁ []) (x :: cat («in».f t₂ []) s) := at [1,2] use cat.cons x _ s
        _ = cat («in».f t₁ []) (x :: «in».f t₂ s)          := at [1,2,2] use ih₂ s
        _ = «in».f t₁ (x :: «in».f t₂ s)                   := ih₁ (x :: «in».f t₂ s)
        _ = «in».f (.int x t₁ t₂) s                        := at [2] use «in».int s x t₁ t₂

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
  | int x t₁ t₂ ih₁ ih₂ =>
      let mt₁ : Tree α := mir t₁
      let mt₂ : Tree α := mir t₂
      guard_hyp ih₁ : ∀ (s : List α), «in».f mt₁ s = rcat («in».f t₁ []) s
      guard_hyp ih₂ : ∀ (s : List α), «in».f mt₂ s = rcat («in».f t₂ []) s
      show «in».f (mir (Tree.int x t₁ t₂)) s = rcat («in».f (Tree.int x t₁ t₂) []) s
      calc
        «in».f (mir (.int x t₁ t₂)) s
          = «in».f (.int x mt₂ mt₁) s                        := at [1,1] use mir.int x t₁ t₂
        _ = «in».f mt₂ (x :: «in».f mt₁ s)                   := «in».int s x mt₂ mt₁
        _ = «in».f mt₂ (x :: rcat («in».f t₁ []) s)          := at [1,2,2] use ih₁ s
        _ = rcat («in».f t₂ []) (x :: rcat («in».f t₁ []) s) := ih₂ (x :: rcat («in».f t₁ []) s)
        _ = rcat (x :: «in».f t₂ []) (rcat («in».f t₁ []) s) := at [2] use rcat.cons x _ _
        _ = rcat (cat («in».f t₁ []) (x :: «in».f t₂ [])) s  := Rcat _ _ _
        _ = rcat («in».f t₁ (x :: «in».f t₂ [])) s           := at [1,1] use CatIn _ _
        _ = rcat («in».f (.int x t₁ t₂) []) s                := at [2,1] use «in».int [] x _ _

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
  | .int x t₁ t₂, s => f t₁ (f t₂ (x :: s))

lemma post.ext {α : Type} (s : List α) :
  post.f (.ext : Tree α) s = s := rfl

lemma post.int {α : Type} (x : α) (t₁ t₂ : Tree α) (s : List α) :
  post.f (.int x t₁ t₂) s = post.f t₁ (post.f t₂ (x :: s)) := rfl

lemma post.def {α : Type} (t : Tree α) : post t = post.f t [] := rfl

attribute [irreducible] post post.f

lemma CatPostGen {α : Type} (t : Tree α) (s1 s2 : List α) :
  cat (post.f t s1) s2 = post.f t (cat s1 s2) := by
  induction t generalizing s1 with
  | ext => calc
      cat (post.f .ext s1) s2
        = cat s1 s2               := at [1,1] use post.ext s1
      _ = post.f .ext (cat s1 s2) := at [2] use post.ext _
  | int x t₁ t₂ ih₁ ih₂ =>
      guard_hyp ih₁ : ∀ (s1 : List α), cat (post.f t₁ s1) s2 = post.f t₁ (cat s1 s2)
      guard_hyp ih₂ : ∀ (s1 : List α), cat (post.f t₂ s1) s2 = post.f t₂ (cat s1 s2)
      show cat (post.f (.int x t₁ t₂) s1) s2 = post.f (.int x t₁ t₂) (cat s1 s2)
      calc
        cat (post.f (.int x t₁ t₂) s1) s2
          = cat (post.f t₁ (post.f t₂ (x :: s1))) s2 := at [1,1] use post.int x t₁ t₂ s1
        _ = post.f t₁ (cat (post.f t₂ (x :: s1)) s2) := ih₁ (post.f t₂ (x :: s1))
        _ = post.f t₁ (post.f t₂ (cat (x :: s1) s2)) := at [1,2] use ih₂ (x :: s1)
        _ = post.f t₁ (post.f t₂ (x :: cat s1 s2))   := at [1,2,2] use cat.cons _ _ _
        _ = post.f (.int x t₁ t₂) (cat s1 s2)        := at [2] use post.int x t₁ t₂ _

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
  | int x t₁ t₂ ih₁ ih₂ =>
      let mt₁ : Tree α := mir t₁
      let mt₂ : Tree α := mir t₂
      guard_hyp ih₁ : ∀ (s : List α), pre.f mt₁ s = rcat (post.f t₁ []) s
      guard_hyp ih₂ : ∀ (s : List α), pre.f mt₂ s = rcat (post.f t₂ []) s
      show pre.f (mir (.int x t₁ t₂)) s = rcat (post.f (.int x t₁ t₂) []) s
      calc
        pre.f (mir (.int x t₁ t₂)) s
          = pre.f (.int x mt₂ mt₁) s                                  := at [1,1] use mir.int _ _ _
        _ = x :: pre.f mt₂ (pre.f mt₁ s)                              := pre.int s x mt₂ mt₁
        _ = x :: pre.f mt₂ (rcat (post.f t₁ []) s)                    := at [1,2,2] use ih₁ s
        _ = x :: rcat (post.f t₂ []) (rcat (post.f t₁ []) s)          := at [1,2] use ih₂ _
        _ = x :: rcat (cat (post.f t₁ []) (post.f t₂ [])) s           := at [1,2] use Rcat _ _ _
        _ = rcat [] (x :: rcat (cat (post.f t₁ []) (post.f t₂ [])) s) := at [2] use rcat.nil _
        _ = rcat [x] (rcat (cat (post.f t₁ []) (post.f t₂ [])) s)     := at [2] use rcat.cons x [] _
        _ = rcat (cat (cat (post.f t₁ []) (post.f t₂ [])) [x]) s      := Rcat [x] _ s
        _ = rcat (cat (post.f t₁ []) (cat (post.f t₂ []) [x])) s      := at [2,1] use CatAssoc _ _ _
        _ = rcat (post.f t₁ (cat (post.f t₂ []) [x])) s               := at [1,1] use CatPost t₁ _
        _ = rcat (post.f t₁ (post.f t₂ [x])) s                        := at [1,1,2] use CatPost t₂ _
        _ = rcat (post.f (.int x t₁ t₂) []) s                         := at [2,1] use post.int x t₁ t₂ []

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
  | .ext, enc         => none :: enc
  | .int x t₁ t₂, enc => f t₁ (f t₂ (some x :: enc))

lemma epost.ext {α : Type} (enc : List (Option α)) :
  epost.f .ext enc = none :: enc := rfl

lemma epost.int {α : Type} (x : α) (t₁ t₂ : Tree α) (enc : List (Option α)) :
  epost.f (.int x t₁ t₂) enc = epost.f t₁ (epost.f t₂ (some x :: enc)) := rfl

lemma epost.def {α : Type} (t : Tree α) : epost t = epost.f t [] := rfl

attribute [irreducible] epost epost.f

/-! Postorder decoding -/
def post2b.f {α : Type} : List (Tree α) -> List (Option α) -> Option (Tree α)
| [tree], []                        => some tree
| forest, none :: enc               => post2b.f (.ext :: forest) enc
| t₂ :: t₁ :: forest, some x :: enc => post2b.f (.int x t₁ t₂ :: forest) enc
| _, _                              => none

def post2b {α : Type} (enc : List (Option α)) : Option (Tree α) := post2b.f [] enc

lemma post2b.tree {α : Type} (tree : Tree α) :
  post2b.f [tree] [] = Option.some tree := by unfold post2b.f; rfl

lemma post2b.none {α : Type} (forest : List (Tree α)) (enc : List (Option α)) :
  post2b.f forest (Option.none :: enc) =
    post2b.f (Tree.ext :: forest) enc := by
  cases forest with | nil => rfl | cons _ f => cases f <;> rfl

lemma post2b.some {α : Type}
  (t₁ t₂ : Tree α) (forest : List (Tree α)) (x : α) (enc : List (Option α)) :
  post2b.f (t₂ :: t₁ :: forest) (Option.some x :: enc) =
    post2b.f (.int x t₁ t₂ :: forest) enc := rfl

lemma post2b.nil_some {α : Type} (x : α) (enc : List (Option α)) :
  post2b.f [] (Option.some x :: enc) = Option.none := rfl

lemma post2b.nil_nil {α : Type} :
  post2b.f [] ([] : List (Option α)) = Option.none := rfl

lemma post2b.cons₂_nil {α : Type} (t₂ t₁ : Tree α) (forest : List (Tree α)) :
  post2b.f (t₂ :: t₁ :: forest) [] = Option.none := rfl

lemma post2b.def {α : Type} (enc : List (Option α)) :
  post2b enc = post2b.f [] enc := rfl

attribute [irreducible] post2b post2b.f

/-! Correctness of postorder encoding -/

lemma PostEncGen {α : Type} (t : Tree α) (forest : List (Tree α)) (enc : List (Option α)) :
  post2b.f forest (epost.f t enc) = post2b.f (t :: forest) enc := by
  induction t generalizing forest enc with
  | ext =>
      show post2b.f forest (epost.f Tree.ext enc) = post2b.f (Tree.ext :: forest) enc
      calc
        post2b.f forest (epost.f .ext enc)
          = post2b.f forest (none :: enc) := at [1,2] use epost.ext enc
        _ = post2b.f (.ext :: forest) enc := post2b.none forest enc
  | int x t₁ t₂ ih₁ ih₂ =>
      guard_hyp ih₁ : ∀ (forest : List (Tree α)) (enc : List (Option α)),
                      post2b.f forest (epost.f t₁ enc) = post2b.f (t₁ :: forest) enc
      guard_hyp ih₂ : ∀ (forest : List (Tree α)) (enc : List (Option α)),
                      post2b.f forest (epost.f t₂ enc) = post2b.f (t₂ :: forest) enc
      show post2b.f forest (epost.f (.int x t₁ t₂) enc) = post2b.f (.int x t₁ t₂ :: forest) enc
      calc
        post2b.f forest (epost.f (.int x t₁ t₂) enc)
          = post2b.f forest (epost.f t₁ (epost.f t₂ (some x :: enc))) := at [1,2] use epost.int _ _ _ _
        _ = post2b.f (t₁ :: forest) (epost.f t₂ (some x :: enc))      := ih₁ forest _
        _ = post2b.f (t₂ :: t₁ :: forest) (some x :: enc)             := ih₂ _ _
        _ = post2b.f ((.int x t₁ t₂) :: forest) enc                   := post2b.some _ _ _ _ _

theorem PostEnc {α : Type} (t : Tree α) : post2b (epost t) = some t := by
  induction t with
  | ext => calc
      post2b (epost .ext)
        = post2b (epost.f .ext []) := at [1,1] use epost.def .ext
      _ = post2b [none]            := at [1,1] use epost.ext []
      _ = post2b.f [] [none]       := post2b.def [none]
      _ = post2b.f [.ext] []       := post2b.none _ _
      _ = some .ext                := post2b.tree .ext
  | int x t₁ t₂ ih₁ ih₂ =>
      guard_hyp ih₁ : post2b (epost t₁) = some t₁
      guard_hyp ih₂ : post2b (epost t₂) = some t₂
      show post2b (epost (.int x t₁ t₂)) = some (.int x t₁ t₂)
      calc
        post2b (epost (.int x t₁ t₂))
          = post2b (epost.f (.int x t₁ t₂) [])             := at [1,1] use epost.def _
        _ = post2b (epost.f t₁ (epost.f t₂ [some x]))      := at [1,1] use epost.int _ _ _ []
        _ = post2b.f [] (epost.f t₁ (epost.f t₂ [some x])) := post2b.def _
        _ = post2b.f [t₁] (epost.f t₂ [some x])            := PostEncGen t₁ _ _
        _ = post2b.f [t₂, t₁] [some x]                     := PostEncGen t₂ _ _
        _ = post2b.f [.int x t₁ t₂] []                     := post2b.some _ _ _ _ _
        _ = some (.int x t₁ t₂)                            := post2b.tree _

end BTree
