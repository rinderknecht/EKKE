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
