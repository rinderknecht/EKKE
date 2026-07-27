let preproc' x =
  let m = String.length x in
  let next = Array.make m 0 in
  let () = next.(0) <- -1 in
  for i = 1 to m-1 do
    let j = ref next.(i-1) in
    while !j >= 0 && x.[!j] <> x.[i-1] do j := next.(!j) done;
    next.(i) <- !j + 1
  done;
  for i = 1 to m-1 do
    let j = ref next.(i) in
    if !j >= 0 && x.[!j] = x.[i] then next.(i) <- next.(!j);
  done;
  next

let preproc x =
  let m = String.length x in
  let next = Array.make m 0 in
  let () = next.(0) <- -1 in
  let j = ref 0 in
  for i = 1 to m-1 do
    if x.[!j] = x.[i]
    then next.(i) <- next.(!j)
    else (next.(i) <- !j;
          while !j >= 0 && x.[!j] <> x.[i] do j := next.(!j) done);
    j := !j + 1;
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
