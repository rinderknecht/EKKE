import Mathlib.Order.Basic -- Importing here type class `LinearOrder`

namespace MergeSort

def merge {α : Type} [LinearOrder α] : List α -> List α -> List α
| [], t      => t
| s, []      => s
| x::s, y::t => if x ≤ y then x :: merge s (y::t) else y :: merge (x::s) t

def cut {α : Type} [LinearOrder α] : List α -> List α × List α
| x::y::s =>
    let (l, r) := cut s
    (x::l, y::r)
| s => (s, [])

lemma cut_shorter {α : Type} [LinearOrder α] (s : List α) :
  (cut_shorter s).1.length <

-- def tms {α : Type} [LinearOrder α] : List α -> List α
-- | []  => []
-- | [x] => [x]
-- | s   => let (l, r) := cut s
--          merge (tms l) (tms r)
-- termination_by s => s.length

end MergeSort
