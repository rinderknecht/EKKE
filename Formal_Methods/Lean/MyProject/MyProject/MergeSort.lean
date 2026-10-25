import Mathlib.Order.Basic -- Importing here type class `LinearOrder`

/-! Merge sort -/
namespace MergeSort

def merge {α : Type} [LinearOrder α] : List α -> List α -> List α
| [], t      => t
| s, []      => s
| x::s, y::t => if x ≤ y then x :: merge s (y::t) else y :: merge (x::s) t

mutual

def cut {α : Type} [LinearOrder α] : List α -> List α -> List α -> List α
| s, y :: t, _ :: _ :: u => cut (y :: s) t u
| s, t, _                => merge (tms s) (tms t)

def tms {α : Type} [LinearOrder α] : List α -> List α
| x :: y :: u => cut [x] (y :: u) u
| u           => u

end -- mutual

def split {α : Type} [LinearOrder α] : List α -> List α × List α
| [] => ([], [])
| x :: s =>
    let (left, right) := split s
    (x :: right, left)

def tms' {α : Type} [LinearOrder α] (s : List α) : List α :=
  let (left, right) := split s
  have : left.length < s.length := by sorry
  have : right.length < s.length := by sorry
  merge (tms' left) (tms' right)
termination_by s.length

-- def split {α : Type} [LinearOrder α] : List α -> List α × List α
-- | x :: y :: s =>
--    let (left, right) := split s
--    (x :: left, y :: right)
-- | s => (s, [])

end MergeSort
