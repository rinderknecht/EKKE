  def length {α} : List α -> Nat
  | []     => 0
  | _ :: l => Nat.succ (length l)

 def cut {α} (s : List α) (n : Nat) (h : Fin (s.length + 1)) : List α × List α :=
    match s, n with
    | _, 0 => ([], s)
    | x :: s, k + 1 =>
        let (t, u) := cut s k (by omega)
        (x :: t, u)
    | [], _ => by omega

def UpSorted {α : Type} [LinearOrder α] : List α → Prop := Ordered (· ≤ ·)
def DownSorted {α : Type} [LinearOrder α] : List α → Prop := Ordered (· ≧ ·)

  def tms {α : Type} [LinearOrder α]: List α -> List α
  | x::y::t => cut [x] (y::t) t
  | t => t

  def cut {α : Type} [LinearOrder α] : List α -> List α -> List α -> List α
  | s, y::t, _::_::u => cut (y::s) t u
  | s, t, u => merge (tms s) (tms t)

lemma Insert.extends {α : Type} [LinearOrder α] (x : α) (s : List α) :
  Perm (insert x s) (x :: s) :=
by induction s with
   | nil =>
      -- ⊢ Perm (insert x []) [x]
      -- insert.nil x : insert x [] = [x]
      -- Perm.reflexivity [x] : Perm [x] [x]
      -- insert.nil x ▸ Perm.reflexivity [x] : Perm (insert x []) [x]
      exact insert.nil x ▸ Perm.reflexivity [x]

def post2b.f {α : Type} (forest : List (Tree α)) (enc : List (Option α)) :
  Option (Tree α) × List (Option α) :=
  match forest with
  | [] =>
      match enc with
      | none :: enc  => post2b.f [Tree.ext] enc
      | some _ :: _  => (none, enc)
      | []           => (none, enc)
  | [tree] => (some tree, enc)
  | t2 :: t1 :: forest =>
      match enc with
      | none :: enc   => post2b.f (Tree.ext :: t2 :: t1 :: forest) enc
      | some x :: enc => post2b.f (Tree.int x t1 t2 :: forest) enc
      | []            => (none, enc)
termination_by structural enc

def post2b {α : Type} (s : List (Option α)) : Option (Tree α) × List (Option α) := post2b.f [] s

lemma post2b.none {α : Type}
  (forest : List (Tree α)) (enc : List (Option α))
  (_ : match forest with | [_] => False | _ => True) :
  post2b.f forest (none :: enc) = post2b.f (Tree.ext :: forest) enc := by
  match forest with
  | []          => rfl
  | [_]         => contradiction
  | _ :: _ :: _ => rfl
