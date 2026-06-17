import LMLExposition.Extract

/-!
# Tests for `LMLExposition.Extract`

The bulk of extraction renders declarations from the elaborated environment and is exercised
end-to-end against a real project (constructing a synthetic `Environment`/`Syntax` for those paths is
impractical). Here we unit-test the pure string/syntax helpers.

Each check is a `#guard`, so any regression turns into a build error. Run with `lake build Test`.
-/

open Lean Std
open LMLExposition

namespace LMLExposition.Test

/-! ## `collapseBlankRuns` -/

-- A run of two or more blank lines collapses to a single blank line; everything else is unchanged.
#guard collapseBlankRuns "a\n\n\nb" == "a\n\nb"
#guard collapseBlankRuns "a\n\n\n\n\nb" == "a\n\nb"
#guard collapseBlankRuns "a\n\nb" == "a\n\nb"        -- already a single blank line: unchanged
#guard collapseBlankRuns "a\nb" == "a\nb"            -- no blank line: unchanged
#guard collapseBlankRuns "a\n\n\n" == "a\n"          -- trailing blank run collapses too
-- Whitespace-only lines count as blank; a run collapses to its first line (kept verbatim).
#guard collapseBlankRuns "a\n  \n\t\nb" == "a\n  \nb"

/-! ## `binderBoundNames` -/

-- Names before the first `:` are the bound (local) variables; the type after it is references.
#guard binderBoundNames "{ι Ω β : Type*}" == #["ι", "Ω", "β"]
#guard binderBoundNames "(hs : IndexedPartition s)" == #["hs"]
#guard binderBoundNames "[inst : Foo α]" == #["inst"]
#guard binderBoundNames "[TopologicalSpace β]" == #[]      -- anonymous instance binder: no bound name
#guard binderBoundNames "{α β}" == #["α", "β"]             -- no `:`: all identifiers are bound

/-! ## `collectSyntaxKinds` -/

-- Every node's kind is collected; a notation use surfaces as a node of the notation parser's kind.
#guard (collectSyntaxKinds (.node .none `A.b #[.node .none `C.d #[]])).contains `A.b
#guard (collectSyntaxKinds (.node .none `A.b #[.node .none `C.d #[]])).contains `C.d
#guard !(collectSyntaxKinds (.node .none `A.b #[])).contains `X.y

end LMLExposition.Test
