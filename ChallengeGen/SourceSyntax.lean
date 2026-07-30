module

public import Lean

@[expose] public section

/-!
# Re-parsing a project's source, and reading declaration keywords off the syntax

Two things `Referee.Collect` and `Referee.Extract` both need, and answered separately before this
module existed: re-parsing a source file against the already-loaded environment, and searching a
command's syntax tree for a node of a given kind.

Neither is incidental to one of them. `collect` reads a declaration's *keyword* this way — which
cannot be recovered from the compiled environment, since Mathlib's `lemma` is a macro that rewrites
itself to `theorem` before elaboration — and `extract` decides from the same syntax whether a command
is a theorem whose proof should be replaced by `sorry`. They were asking the same question of the
same parse.

Keeping the answer in one place matters beyond tidiness: the two copies had already drifted.
`Extract.isTheoremDecl` matched Mathlib's `lemma` but not the Batteries command it overrides, so in a
project that uses Batteries without Mathlib a `lemma`'s whole proof was emitted into its minimal file
instead of `sorry`. Both callers now consult `theoremSyntaxKinds`.
-/

open Lean

namespace Referee

/-! ## Declaration keywords, as syntax kinds

The keyword a declaration was written with survives only in the parse tree. These are the kinds to
look for; the lists are plural because more than one package defines the same keyword.
-/

/-- Command kinds meaning "written with `lemma`".

Mathlib's `lemma` is declared at the root (`syntax (name := lemma) …` in `Mathlib/Tactic/Lemma.lean`)
and takes priority over the Batteries one, which it exists to override — but a project may have
either, so both count. -/
def lemmaSyntaxKinds : Array SyntaxNodeKind := #[`lemma, `Batteries.Tactic.Lemma.lemmaCmd]

/-- Command kinds meaning "written with `theorem`", the plain keyword and every `lemma` synonym.

This is the "has a proof that may be replaced by `sorry`" test, which is why it includes `lemma`:
the distinction between the two is editorial, and matters only to what the site *labels* them. -/
def theoremSyntaxKinds : Array SyntaxNodeKind :=
  #[``Lean.Parser.Command.theorem] ++ lemmaSyntaxKinds

/-- Command kinds meaning "written with `instance`". -/
def instanceSyntaxKinds : Array SyntaxNodeKind := #[``Lean.Parser.Command.instance]

/-- Command kinds meaning "written with `alias`", both the plain and the `⟨fwd, rev⟩` forms. -/
def aliasSyntaxKinds : Array SyntaxNodeKind :=
  #[`Batteries.Tactic.Alias.alias, `Batteries.Tactic.Alias.aliasLR]

/-- Command kinds declaring a `structure` or a `class`; both parse as `Command.structure`, differing
only in whether they begin with `structureTk` or `classTk`. -/
def structureSyntaxKinds : Array SyntaxNodeKind := #[``Lean.Parser.Command.structure]

/-! ## Searching a command's syntax -/

/-- The first descendant of `root` whose kind is one of `kinds`, breadth-first.

Searching the whole tree rather than only the head is what sees through the wrapper commands a
declaration can be nested in — `set_option … in`, `open … in`, `omit … in`. It stays specific
despite that: a declaration keyword is a *command* node, and no term ever contains one, so a `def`'s
syntax cannot match `theoremSyntaxKinds`. -/
partial def findFirstOfKinds? (root : Syntax) (kinds : Array SyntaxNodeKind) : Option Syntax :=
  Id.run do
  let mut worklist : Array Syntax := #[root]
  while !worklist.isEmpty do
    let stx := worklist.back!
    worklist := worklist.pop
    if kinds.contains stx.getKind then return some stx
    for arg in stx.getArgs do
      worklist := worklist.push arg
  return none

@[inherit_doc findFirstOfKinds?]
def findFirstOfKind? (root : Syntax) (kind : SyntaxNodeKind) : Option Syntax :=
  findFirstOfKinds? root #[kind]

/-- True if any node of `stx` has one of `kinds`. See `findFirstOfKinds?` for why the whole tree. -/
def containsSyntaxKind (stx : Syntax) (kinds : Array SyntaxNodeKind) : Bool :=
  (findFirstOfKinds? stx kinds).isSome

/-! ## Parsing a file -/

/-- Every top-level command of `source`, re-parsed against `env`, with the module header dropped.

Elaboration errors are expected and ignored. `env` already contains every declaration in the file —
it is the environment the project was loaded into — so each declaration command fails with
"declaration already exists" almost immediately, which is exactly why this is cheap enough to run
over a whole project. Only the parsed `Syntax` is consumed, and the parser produces that either way.

Positions on the returned syntax are byte offsets into `source`; a caller wanting lines can convert
through `source.toFileMap`. -/
def parseCommands (env : Environment) (source : String) (filePath : String) : IO (Array Syntax) := do
  let inputCtx := Lean.Parser.mkInputContext source filePath
  let (_, parserState, messages) ← Lean.Parser.parseHeader inputCtx
  let cmdState := Lean.Elab.Command.mkState env messages {}
  let s ← Lean.Elab.IO.processCommands inputCtx parserState cmdState
  return s.commands.filter (·.getKind != ``Lean.Parser.Module.header)

end Referee
