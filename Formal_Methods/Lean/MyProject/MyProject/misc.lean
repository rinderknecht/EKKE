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
