type 'a tree =
  Ext
| Int of 'a * 'a tree * 'a tree

let example =
  Int (6,
       Int (3,
            Int (1,
                 Ext,
                 Int (0,
                      Ext,
                      Ext)),
            Int (2,
                 Ext,
                 Ext)),
       Int (5,
            Ext,
            Int (4,
                 Ext,
                 Ext)))

let rec epost (t : 'a tree) (enc : 'a option list) : 'a option list =
  match t with
    Ext -> None :: enc
  | Int (x, t1, t2) -> epost t1 (epost t2 (Some x :: enc))

let epost (t : 'a tree) : 'a option list = epost t []

let rec post2b (f : 'a tree list) (enc : 'a option list) : 'a tree option =
  match f, enc with
    [tree], [] -> Some tree
  | forest, None :: enc -> post2b (Ext :: forest) enc
  | t2 :: t1 :: forest, Some x :: enc -> post2b (Int (x, t1, t2) :: forest) enc
  | _ -> None

let post2b (enc : 'a option list) : 'a tree option = post2b [] enc
