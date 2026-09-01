module

public import Lean
public import Lean.DeclarationRange

@[expose] public section

/-!
# What a challenge generator needs to know about a declaration

The extraction takes a *compiled* project — a live `Environment` and, for the readable tier, the
source files it was built from — and turns one declaration into a file that compiles on its own.
What it cannot compute for itself is which declarations exist, how they are classified, and what
each one's dependency closure is. That is a producer's job, and different producers answer it
differently: a documentation tool has it already, a standalone consumer computes it with
[`MeaningGraph`](https://github.com/RemyDegenne/meaning-graph).

`ChallengeDecl` is that hand-off, and it is deliberately the smallest record the extraction
actually reads. It is *not* a general declaration record: anything a producer knows that extraction
does not use — docstrings, signatures, source snippets, specification links, trust — stays with the
producer. Keeping it minimal is what stops this package from acquiring the producer's dependencies,
which is the whole point of it being a package.

## Why these four fields

* `name` — the declaration to extract, and the stem of the file written for it (`anchorIdOf`).
* `kind` — the readable tier decides from this whether a command is a theorem whose proof becomes
  `sorry`, among other things. It is the only classification extraction makes use of.
* `moduleName` — which source file to read, and the order to walk modules in.
* `transDeps` — the transitive closure to inline. Extraction does *not* compute this and does not
  decide which edges it follows: a closure that lost a lemma some kept tactic block calls would
  produce a file that does not compile, so the edge policy belongs to whoever knows what the file
  is for. Pass a closure already taken over edges that keep proofs.
-/

open Lean

namespace ChallengeGen

/-! ## Classification -/

/-- Classification of exposed Lean declarations. -/
inductive DeclKind where
  | theorem
  | definition
  | opaque
  | structure
  | typeclass
  | inductive
  | axiom
  | instance
deriving Repr, BEq, Inhabited, ToJson, FromJson

/-- Human-readable label for each declaration kind. -/
def DeclKind.label : DeclKind → String
  | .theorem => "Theorem"
  | .definition => "Definition"
  | .opaque => "Opaque"
  | .structure => "Structure"
  | .typeclass => "Type Class"
  | .inductive => "Inductive"
  | .axiom => "Axiom"
  | .instance => "Instance"

/-! ## The input record -/

/-- One declaration to generate a challenge for, as the extraction needs it. See the module
docstring for why it has exactly these fields and no others. -/
structure ChallengeDecl where
  /-- The declaration. Also the stem of the file written for it, via `anchorIdOf`. -/
  name : Name
  /-- What kind of declaration it is; the readable tier reads this to decide, among other things,
  whether a proof is replaced by `sorry`. -/
  kind : DeclKind
  /-- The module that declares it, which is the source file the readable tier reads. -/
  moduleName : Name
  /-- The transitive dependency closure to inline, over edges chosen by the producer. Must stay
  closed over proofs: a kept tactic block whose lemmas are missing does not compile. -/
  transDeps : Array Name := #[]
deriving Repr, Inhabited, ToJson, FromJson

/-! ## Names, files and ranges

Small helpers the extraction shares with its producer. `anchorIdOf` in particular is a *contract*
rather than a convenience: it is the name of the file written for a declaration, so a producer that
links to those files has to compute the stem the same way. One definition, imported by both.
-/

/-- Computes name Components. -/
def nameComponents : Name → List String
  | .anonymous => []
  | .num p n => nameComponents p ++ [toString n]
  | .str p s => nameComponents p ++ [s]

/-- The namespace `n` and all of its ancestor namespaces, innermost first. -/
partial def namespaceAncestors : Name → List Name
  | .anonymous => []
  | n => n :: namespaceAncestors n.getPrefix

/-- Maps a declaration name to an identifier safe to use as a filename, URL, and HTML anchor:
namespace dots become `___`, and the characters forbidden in filenames on some operating systems
(Windows: `< > : " / \ | ? *`) are replaced by fullwidth Unicode lookalikes that are legal
everywhere. Notation declarations such as `«term𝓛[_|_;_]»` would otherwise produce a `|` in the
filename, which is illegal on Windows and rejected by Lean's module-name portability check. -/
def anchorIdOf (name : Name) : String :=
  let safeChar : Char → Char := fun c =>
    match c with
    | '<' => '＜' | '>' => '＞' | ':' => '：' | '"' => '＂' | '/' => '／'
    | '\\' => '＼' | '|' => '｜' | '?' => '？' | '*' => '＊'
    | _ => c
  (String.intercalate "___" (name.toString.splitOn ".")).map safeChar

/-- Computes module SourcePath. -/
def moduleSourcePath (projectDir : System.FilePath) (moduleName : Name) : System.FilePath :=
  projectDir / s!"{moduleName.toString.replace "." "/"}.lean"

/-- Helper for runCoreIO. -/
def runCoreIO {α : Type} (env : Environment) (x : CoreM α) : IO α := do
  x.toIO'
    { fileName := "<challenge-gen>", fileMap := default, options := {},
      currNamespace := .anonymous, openDecls := [] }
    { env := env, ngen := { namePrefix := `_challengeGen } }

/-- Retrieves declaration source ranges, returning `none` on failure. -/
def findRanges? (env : Environment) (name : Name) : IO (Option DeclarationRanges) := do
  try
    runCoreIO env (findDeclarationRanges? name)
  catch _ =>
    pure none

end ChallengeGen
