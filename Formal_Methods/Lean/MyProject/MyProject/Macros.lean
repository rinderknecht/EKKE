import Lean

/-! Macros -/
namespace Macros

open Lean.Parser.Tactic.Conv

syntax "at" "[" withoutPosition(enterArg,+) "]" ("in" ident)? "use" term : term
syntax "at" "[" withoutPosition(enterArg,+) "]" ("in" ident)? "use" term : tactic

macro_rules
  | `(term| at [$args,*] $[in $h:ident]? use $proof) =>
      match h with
      | some h => `(term| by conv at $h => enter [$args,*]; tactic => exact $proof)
      | none => `(term| by conv => enter [$args,*]; tactic => exact $proof)
  | `(tactic| at [$args,*] $[in $h:ident]? use $proof) =>
      match h with
      | some h => `(tactic| conv at $h => enter [$args,*]; tactic => exact $proof)
      | none => `(tactic| conv => enter [$args,*]; tactic => exact $proof)

end Macros
