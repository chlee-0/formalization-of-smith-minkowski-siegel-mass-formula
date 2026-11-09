import SMSFormula.StandardAxiomsGuardCache

/-!
# A checked standard-axiom guard

`#print axioms` only prints an axiom cone: the build stays green whatever it shows.  The commands
below turn the inspection into a build failure.

* `#assert_standard_axioms c` fails unless every axiom in the cone of `c` is one of Lean's standard
  `propext`, `Classical.choice`, `Quot.sound` (so in particular `sorryAx`, the compiler-trust axioms
  and every project axiom are rejected);
* `#assert_not_declared c` fails if the fully qualified name `c` is declared in the environment.

`collectAxioms` walks the whole dependency closure of its argument afresh, so a file with many
checks repeats the same traversal of shared dependencies (a file with a thousand checks spent
most of its build time there).  `#assert_standard_axioms` therefore remembers, in an environment
extension local to the current file, every constant reached by a check that passed.  Each such
constant lies in the closure of a constant with standard axioms only, so its own closure has standard
axioms only, and a later check need not walk it again.  A non-standard axiom reachable from a later
constant is reachable along a path that avoids every remembered constant, so the later check finds
it exactly as `collectAxioms` would.  The cache is never exported and starts empty in every file;
within a file the environment only grows and existing constants never change, so no invalidation is
needed.  A failed check adds nothing to the cache.
-/

open Lean Elab Command

/-- Fail unless the axiom cone of the constant is within `propext`, `Classical.choice`,
`Quot.sound`. -/
elab "#assert_standard_axioms " id:ident : command => do
  let c ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let env ← getEnv
  -- Take constants from the kernel environment, as `collectAxioms` does.
  let (axs, visited) := StandardAxiomsGuard.collectAvoiding env.checked.get
    (StandardAxiomsGuard.cleanExt.getState env) c
  let bad := axs.filter fun a => !StandardAxiomsGuard.allowed.contains a
  unless bad.isEmpty do
    throwError "{c} depends on non-standard axioms: {bad}"
  modifyEnv fun env => StandardAxiomsGuard.cleanExt.setState env visited
  logInfo m!"{c}: standard axioms only"

/-- Fail if the fully qualified name is declared in the current environment. -/
elab "#assert_not_declared " id:ident : command => do
  let n := id.getId
  if (← getEnv).contains n then
    throwError "{n} is declared"
  logInfo m!"{n} is not declared"

/-! Self-tests of the guard. -/

/-- A theorem with an empty axiom cone. -/
theorem standardAxiomsGuard_selfTest : True := trivial

#assert_standard_axioms standardAxiomsGuard_selfTest
#assert_not_declared standardAxiomsGuard_noSuchConstant
