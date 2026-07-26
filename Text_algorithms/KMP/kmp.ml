let preproc x =
  let len = String.length x in
  let next = Array.make len 7 in
  let () = next.(0) <- -1 in
  for i = 1 to len - 1 do
    let j = ref next.(i - 1) in
    while !j >= 0 && x.[!j] <> x.[i-1] do j := next.(!j) done;
    next.(i) <- !j + 1
  done;
  for i = 1 to len - 1 do
    let j = ref next.(i) in
    while !j >= 0 && x.[!j] = x.[i] do j := next.(!j) done;
    next.(i) <- !j
  done;
  next

let find p t =
  let m = String.length p
  and n = String.length t in
  let next = preproc p in
  let i = ref 0
  and j = ref 0 in
  while !i < m && !j < n do
    if !i = -1 || p.[!i] = t.[!j] then
      (i := !i + 1; j := !j + 1)
    else i := next.(!i)
  done;
  if !i = m then Some (!j - m) else None
