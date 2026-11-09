import Lean

/-!
# Cache for the standard-axiom guard

The environment extension and traversal behind `#assert_standard_axioms`
(`SMSFormula.StandardAxiomsGuard`), in a module of their own because an environment extension
cannot be used in the file that registers it.
-/

open Lean

namespace StandardAxiomsGuard

/-- The standard axioms. -/
def allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

/-- Constants of the current file's environment known to depend only on the standard axioms. -/
initialize cleanExt : EnvExtension NameHashSet ← registerEnvExtension (pure {})

/-- The axioms reachable from `c` without passing through a constant of `clean`, and the set
`clean` enlarged by every constant visited. Same traversal as `Lean.CollectAxioms.collect`, with an
explicit stack. -/
def collectAvoiding (env : Kernel.Environment) (clean : NameHashSet) (c : Name) :
    Array Name × NameHashSet := Id.run do
  let mut visited := clean
  let mut stack : Array Name := #[c]
  let mut axs : Array Name := #[]
  while h : stack.size > 0 do
    let d := stack[stack.size - 1]
    stack := stack.pop
    if visited.contains d then continue
    visited := visited.insert d
    match env.find? d with
    | some (.axiomInfo v) =>
        axs := axs.push d
        stack := stack ++ v.type.getUsedConstants
    | some (.defnInfo v) => stack := stack ++ v.type.getUsedConstants ++ v.value.getUsedConstants
    | some (.thmInfo v) => stack := stack ++ v.type.getUsedConstants ++ v.value.getUsedConstants
    | some (.opaqueInfo v) => stack := stack ++ v.type.getUsedConstants ++ v.value.getUsedConstants
    | some (.quotInfo _) => pure ()
    | some (.ctorInfo v) => stack := stack ++ v.type.getUsedConstants
    | some (.recInfo v) => stack := stack ++ v.type.getUsedConstants
    | some (.inductInfo v) => stack := stack ++ v.type.getUsedConstants ++ v.ctors.toArray
    | none => pure ()
  return (axs, visited)

end StandardAxiomsGuard
