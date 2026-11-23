import LSql
import Lean
/-! The totality audit: every constant lean-sqlite defines (namespace LSql, and main) is a definition the kernel checked,
termination included. A partial def would be an opaque constant, an unsafe one unsafe, an implemented_by/extern one would
have an implementation; none may exist. (f._unsafe_rec is the compiler's executable copy of a recursive definition f; it
is allowed when f itself is a checked definition.) main may not depend on sorryAx. Run by check.sh. -/
open Lean Elab Command

elab "#audit_totality" : command => do
  let env ← getEnv
  let mine := env.constants.toList.filter fun (n, _) => (Name.mkSimple "LSql").isPrefixOf n || n == Name.mkSimple "main"
  let mut bad : Array String := #[]
  let mut count : Nat := 0
  for (n, ci) in mine do
    -- the compiler's executable copy of a recursive definition: its source function must itself be a checked definition
    if n.toString.endsWith "._unsafe_rec" then
      match env.find? (n.getPrefix) with
      | some (.defnInfo _) => continue
      | _ => bad := bad.push s!"partial: {n.getPrefix}"; continue
    count := count + 1
    if ci.isUnsafe then bad := bad.push s!"unsafe: {n}"
    match ci with
    | .opaqueInfo _ => bad := bad.push s!"opaque (partial?): {n}"
    | _ => pure ()
    if (Compiler.getImplementedBy? env n).isSome then bad := bad.push s!"implemented_by: {n}"
    if isExtern env n then bad := bad.push s!"extern: {n}"
  let ax ← liftCoreM (collectAxioms (Name.mkSimple "main"))
  if ax.contains (Name.mkSimple "sorryAx") then bad := bad.push "depends on sorryAx"
  logInfo m!"audited {count} constants: none partial, unsafe, opaque or extern; axioms under main: {ax.toList}"
  unless bad.isEmpty do throwError m!"not total: {bad.toList}"

#audit_totality
