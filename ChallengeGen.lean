module

public import ChallengeGen.Decl
public import ChallengeGen.SourceSyntax
public import ChallengeGen.Extract
public import ChallengeGen.Flat

@[expose] public section

/-!
# Standalone Lean files, one per declaration

Turns a declaration of a compiled project into a file that compiles on its own: its transitive
dependencies inlined, its proofs replaced by `sorry`, its imports cut down to the external frontier.
One such file is a self-contained statement of one problem, which is what makes it usable as a
challenge for something that has to produce the proof.

Two tiers, from the same input:

* `ChallengeGen.writeAllExtractions` — the readable tier. Copies verbatim source text and replays
  the surrounding `namespace`/`open`/`variable`/notation context, so the file reads the way a
  mathematician wrote it. Needs the project's source files on disk.
* `ChallengeGen.Flat.writeAllFlatExtractions` — the robust tier. Renders each declaration from its
  `ConstantInfo`, fully qualified and `@`-explicit, and never opens a source file. Gives up
  readability and, with it, the whole class of context-replay failures.

Both take an `Array ChallengeDecl` — four fields, see `ChallengeGen.Decl` — and a live
`Environment` with the project imported, so both must run inside the target project's `lake env`.
Neither decides which declarations to extract or which dependency edges the closure follows; those
are the producer's calls.
-/
