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

/-! ## `binderTypeHead?`

The head symbol of a binder's *type*, used by `pruneVariable` to resolve generalized field
notation (`𝓕.IsComplete` ⇒ `Filtration.IsComplete`) back to the declaration it references. -/

#guard binderTypeHead? "{𝓕 : Filtration ι mΩ}" == some `Filtration
#guard binderTypeHead? "(hs : IndexedPartition s)" == some `IndexedPartition
#guard binderTypeHead? "[inst : Foo α]" == some `Foo
-- A qualified head keeps its dots, so it resolves as one name rather than as a receiver+field.
#guard binderTypeHead? "{μ : MeasureTheory.Measure Ω}" == some `MeasureTheory.Measure
-- No `:` separator, so there is no type to read.
#guard binderTypeHead? "[TopologicalSpace β]" == none
#guard binderTypeHead? "{α β}" == none
-- A function type reports the head of its *first* argument; `pruneVariable` only ever uses this to
-- look up an exact excluded name, so an imprecise head simply fails to match and drops nothing.
#guard binderTypeHead? "{X : ι → Ω → E}" == some `ι

/-! ## `collectSyntaxKinds` -/

-- Every node's kind is collected; a notation use surfaces as a node of the notation parser's kind.
#guard (collectSyntaxKinds (.node .none `A.b #[.node .none `C.d #[]])).contains `A.b
#guard (collectSyntaxKinds (.node .none `A.b #[.node .none `C.d #[]])).contains `C.d
#guard !(collectSyntaxKinds (.node .none `A.b #[])).contains `X.y

end LMLExposition.Test
