module

public import Referee.Extract
-- The checks below are `#guard`s, which Lean elaborates into compile-time (`meta`)
-- definitions, so the declarations under test have to be imported at that level too.
meta import Referee.Extract

@[expose] public section

/-!
# Tests for `Referee.Extract`

The bulk of extraction renders declarations from the elaborated environment and is exercised
end-to-end against a real project (constructing a synthetic `Environment`/`Syntax` for those paths is
impractical). Here we unit-test the pure string/syntax helpers.

Each check is a `#guard`, so any regression turns into a build error. Run with `lake build Test`.
-/

open Lean Std
open Referee

namespace Referee.Test

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

/-! ## `isDroppedAttribute`

Attributes whose elaboration-time side effect cannot work in a standalone extraction are removed;
the ones that *generate* declarations the closure may depend on must survive. -/

-- `@[ext]` on a theorem only registers it and proves an `_iff` converse: inert here, and the proof
-- needs a `@[refl]` lemma that is not in the closure.
#guard isDroppedAttribute false "ext"
#guard isDroppedAttribute false "ext (iff := false)"
-- ...but on a structure it is what *defines* `Foo.ext`/`Foo.ext_iff`, so it must stay.
#guard !isDroppedAttribute true "ext"
-- Matching is on whole tokens, so a different attribute that merely starts with "ext" is untouched.
#guard !isDroppedAttribute false "extern \"lean_foo\""

-- Every `to_additive` form is kept. Plain `to_additive` generates the additive sibling; the
-- `existing` form looks inert but registers the translation that *later* `to_additive` commands
-- need, so dropping it breaks them (see `isDroppedAttribute`).
#guard !isDroppedAttribute false "to_additive existing"
#guard !isDroppedAttribute false "to_additive"
#guard !isDroppedAttribute false "to_additive (attr := simps)"

#guard !isDroppedAttribute false "simp"
#guard !isDroppedAttribute false "refl"

-- `@[specifies]` records a link for Referee to read back and does nothing in a standalone file. It
-- is dropped in every form, which is what lets `isExcludedImport` withhold `import LeanSpec`.
#guard isDroppedAttribute false "specifies"
#guard isDroppedAttribute false "specifies entropy"
#guard isDroppedAttribute false "specifies entropy \"agrees with the textbook formula\""
#guard isDroppedAttribute true "specifies"
#guard !isDroppedAttribute false "specifies_foo"

-- `@[characterization]` is the same story, and the `true` case matters more here: the property of a
-- characterization is often a `structure` or a `class`.
#guard isDroppedAttribute false "characterization existence"
#guard isDroppedAttribute false "characterization uniqueness IsEntropy"
#guard isDroppedAttribute false "characterization property entropy \"the Shannon axioms\""
#guard isDroppedAttribute true "characterization property entropy"
#guard !isDroppedAttribute false "characterizations"

-- The `local`/`scoped` attribute kind is part of the attribute's source text; matching skips it, so
-- a dropped attribute is dropped in every kind.
#guard isDroppedAttribute false "local specifies double"
#guard isDroppedAttribute false "scoped specifies"
#guard isDroppedAttribute false "local ext"
#guard !isDroppedAttribute true "local ext"
#guard !isDroppedAttribute false "local simp"

/-! ## `isExcludedImport` / `isExcludedOption`

`LeanSpec` carries the `@[specifies]` and `@[characterization]` attributes and nothing a
formalization refers to; since every annotation is stripped, the extracted file must not import
it — the web editor has Mathlib only. Whatever the dropped import registered has to go with it,
options included. -/

#guard isExcludedImport `LeanSpec
#guard isExcludedImport `LeanSpec.Basic          -- a submodule, were the package ever to grow one
-- Component-wise, so a project whose name merely starts the same way is untouched.
#guard !isExcludedImport `LeanSpecExtra
#guard !isExcludedImport `Mathlib
#guard !isExcludedImport `Mathlib.Order.LeanSpec

#guard isExcludedOption `specifies.checkTargetMentioned
#guard isExcludedOption `characterization.checkNotCircular
#guard !isExcludedOption `maxHeartbeats
#guard !isExcludedOption `linter.all

/-! ## `setOptionName?`

The file-level `set_option` survives as a context command rather than inside a declaration's source,
so the option it names is read back out of that text. -/

#guard setOptionName? "set_option specifies.checkTargetMentioned false" ==
  some `specifies.checkTargetMentioned
#guard setOptionName? "set_option maxHeartbeats 400000" == some `maxHeartbeats
#guard setOptionName? "set_option\n  pp.all\n  true" == some `pp.all   -- laid out over lines
#guard setOptionName? "variable {α : Type*}" == none                   -- not a `set_option` at all

/-! ## `isTranslationAttribute`

Standalone `attribute …` commands are replayed only when they register a translation, since those
are the ones whose loss makes *other* declarations fail to elaborate. -/

#guard isTranslationAttribute "to_dual existing"
#guard isTranslationAttribute "to_dual"
#guard isTranslationAttribute "to_additive"
#guard isTranslationAttribute "to_additive (attr := simps)"
-- Proof-elaboration attributes are not replayed: moot when every proof is `sorry`, and replaying
-- them pulls whole modules into targets that do not need them.
#guard !isTranslationAttribute "simp"
#guard !isTranslationAttribute "fun_prop"
#guard !isTranslationAttribute "measurability"
#guard !isTranslationAttribute "aesop (rule_sets := [finiteness]) safe apply"
-- Matched on the leading token, so a longer name starting the same way does not hit.
#guard !isTranslationAttribute "to_dual_extra"

/-! ## `collectSyntaxKinds` -/

-- Every node's kind is collected; a notation use surfaces as a node of the notation parser's kind.
#guard (collectSyntaxKinds (.node .none `A.b #[.node .none `C.d #[]])).contains `A.b
#guard (collectSyntaxKinds (.node .none `A.b #[.node .none `C.d #[]])).contains `C.d
#guard !(collectSyntaxKinds (.node .none `A.b #[])).contains `X.y

end Referee.Test
