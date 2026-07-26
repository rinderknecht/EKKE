let preproc x =
  let len = String.length x in
  let next = Array.make len 0 in
  let () = next.(0) <- -1 in
  for i = 1 to len - 1 do
    let j = ref next.(i - 1) in
    while !j >= 0 && x.[!j] <> x.[i-1] do j := next.(!j) done;
    next.(i) <- !j + 1
  done;
  next
