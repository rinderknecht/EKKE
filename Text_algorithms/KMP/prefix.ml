let prefix x t =
  let i = ref 0 in
  while !i < min (String.length x) (String.length t) do
    i := 1 + if x.[!i] = t.[!i] then !i else String.length x
  done;
  !i = String.length x
