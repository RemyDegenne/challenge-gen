import LeanExposition.Extract

/-!
# Tests for `LeanExposition.Extract`

The bulk of extraction now renders declarations from the elaborated environment (`renderDecl`,
`renderStructure`, …), which needs an `Environment`; that path is exercised end-to-end against a real
project. Here we unit-test the pure helpers that select and order what gets emitted.
-/

open Lean Std
open LeanExposition

namespace LeanExposition.Test

private def mkDecl (name : Name) (transDeps : Array Name := #[]) : DeclInfo := {
  name := name
  moduleName := `M
  modulePath := "M"
  groupKey := "M"
  kind := .definition
  displaySignature := ""
  expandedSignature := ""
  docBlocks := #[]
  proofText? := none
  source? := none
  hasSorry := false
  deps := #[]
  transDeps := transDeps
}

/-! ## `emitOrder` -/

private def byName : HashMap Name DeclInfo :=
  .ofList [(`A, mkDecl `A), (`B, mkDecl `B), (`C, mkDecl `C)]

-- The emit list is the target's transitive dependencies (in their topological order) followed by
-- the target itself.
#guard (emitOrder byName (mkDecl `C (transDeps := #[`A, `B]))).map (·.name) == #[`A, `B, `C]

-- Dependencies that are not exposed declarations (absent from the map) are dropped.
#guard (emitOrder byName (mkDecl `C (transDeps := #[`A, `External]))).map (·.name) == #[`A, `C]

-- A leaf with no dependencies emits just itself.
#guard (emitOrder byName (mkDecl `A)).map (·.name) == #[`A]

end LeanExposition.Test
