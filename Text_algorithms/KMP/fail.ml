let rec fail x i =
  assert (0 <= i && i < String.length x);
  if i = 0 then -1
  else let j = ref (i - 1) in
       let rec repeat () =
         j := fail x !j;
         if not (!j = -1 || x.[!j] = x.[i-1]) then repeat ()
       in repeat (); 1 + !j
