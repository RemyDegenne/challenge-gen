# ChallengeGen

One declaration of a compiled Lean project, turned into a file that compiles on its own: its
transitive dependencies inlined, its proofs replaced by `sorry`, its imports cut down to the
external frontier. One such file is a self-contained statement of one problem — which is what makes
it usable as a challenge for something that has to produce the proof.

Depends on Lean core and [`MeaningGraph`](https://github.com/RemyDegenne/meaning-graph), and
nothing else. It was extracted from the
[`exposition`](https://github.com/LeanMachineLearning/exposition) repository, whose `referee` tool
is its first consumer, and is a package of its own so that generating challenges does not drag in
that tool's build (Verso, SubVerso, MD4Lean, …).

## Two tiers

Both take the same input and differ only in how they render a declaration.

- **`writeAllExtractions`** — the readable tier. Copies the **verbatim source text** of each
  declaration and replays the surrounding `namespace`/`open`/`variable`/notation context, so
  notation survives and the file reads the way a mathematician wrote it. Needs the project's source
  files on disk.
- **`Flat.writeAllFlatExtractions`** — the robust tier. Renders each declaration from its
  `ConstantInfo`: fully qualified, `@`-explicit, no notation, no instance search, no context to
  replay. Never opens a source file. Gives up readability and, with it, the entire class of
  context-replay failures.

The intended use is both: prefer the readable file, fall back to the flat one for the declarations
whose readable version does not compile.

## What you have to supply

```lean
structure ChallengeDecl where
  name : Name
  kind : DeclKind
  moduleName : Name
  transDeps : Array Name := #[]
```

Four fields, and that is the whole interface. This package does **not** decide which declarations
are worth extracting, and it does **not** compute or choose the dependency closure — a closure that
dropped a lemma some kept tactic block calls would produce a file that does not compile, so the
edge policy belongs to whoever knows what the files are for. Take the closure over edges that keep
proofs; `MeaningGraph.transitiveDeps` is what computes it.

Both entry points also need a live `Environment` with the project imported, so a tool built on this
runs inside the target project's `lake env`, the way `referee extract` does.

```lean
import ChallengeGen

open Lean ChallengeGen

def writeChallenges (env : Environment) (root : Name) (decls : Array ChallengeDecl)
    (projectDir out : System.FilePath) : IO Nat :=
  writeAllExtractions env root decls projectDir out
```

Each file is named `<anchorIdOf decl.name>.lean`. `anchorIdOf` is exported for exactly that reason:
a tool that links to these files has to compute the stem the same way the writer does, so there is
one definition of it and both sides import it.

## Checks

`lake build ChallengeGenTest` runs the `#guard`s: the pure string and syntax helpers, and the name
mapping that decides what a file is called. They are elaboration-time, so building the target is
running them.

The bulk of the extraction is exercised end to end against real projects instead — constructing a
synthetic `Environment` for those paths is impractical, and what actually matters is whether the
files compile. The consumer this was extracted from measures that with a script that runs
`lake env lean` over every generated file.

The test module is `ChallengeGen.Test`, not `Test`: module roots are shared across a whole Lake
workspace, so a package that claims the top-level name `Test` takes it away from every project that
requires it.
