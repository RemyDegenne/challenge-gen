module

public import Referee.Extract

@[expose] public section

/-!
# Standalone Lean file extraction (flat, environment-derived variant)

This is the **tier-2 fallback** for `Referee.Extract`. Where that module copies verbatim
source text and replays the surrounding `namespace`/`open`/`variable`/notation context — which is
what makes its output readable, and also what makes it fail — this module never looks at a source
file at all. It renders each declaration from its `ConstantInfo` in the loaded environment.

## Why this is more robust

Everything the verbatim path has to get right exists only because source text has to re-elaborate
in a context that no longer surrounds it. Emitting from the environment removes the whole class:

* no `variable`/`omit` pruning — binders are part of the printed type;
* no `namespace`/`section`/`open` balancing — every name is emitted fully qualified at top level;
* no notation replay — every application is printed as `@f a b c`, so no parser extension is needed;
* no attribute replay and no instance search — `@`-explicit applications never synthesize anything,
  so `@[simp]`/`@[measurability]`/`@[to_additive]` registrations are irrelevant;
* no tactic blocks — theorem proofs are `sorry` and proof subterms inside definition values are
  `(sorry : <statement>)`, which is defeq by proof irrelevance and keeps output small.

The cost is readability, which is exactly the trade this tier is for.

## Strategy

1. Render every emittable project-local constant once (`renderAll`), recording which project-local
   constants each rendering references. Rendering *is* the dependency analysis: a constant is a
   dependency iff the printed form mentions it.
2. Per target, take the transitive closure of that reference map in topological order
   (`MeaningGraph.topologicalClosure`) and concatenate the renderings.
3. Prepend the external (non-project) import frontier, reusing `externalImports`.

Auto-generated constants (constructors, recursors, projections, `noConfusion`, …) are never
emitted — the `inductive`/`structure` command regenerates them — but a reference to one is
redirected to the declaration that owns it, so that owner enters the closure.
-/

open Lean Lean.Meta

namespace Referee.Flat

open MeaningGraph

/-! ## Rendering names as legal identifiers -/

/-- Tokens that cannot appear as a bare identifier component, so a declaration name containing one
must be escaped. Not exhaustive — it covers the keywords a declaration name plausibly collides
with. -/
def reservedComponents : List String :=
  ["end", "def", "theorem", "lemma", "example", "axiom", "abbrev", "instance", "structure", "class",
   "inductive", "opaque", "where", "fun", "let", "have", "show", "from", "match", "with", "do",
   "if", "then", "else", "by", "at", "in", "open", "namespace", "section", "variable", "universe",
   "deriving", "extends", "this", "sorry", "calc", "attribute", "macro", "notation", "set_option",
   "mutual", "partial", "private", "protected", "noncomputable", "unsafe", "Type", "Prop", "Sort",
   "forall", "exists", "fn", "return", "try", "catch", "finally", "for", "while", "unless"]

/-- True if `s` can be written as a bare identifier component. Reserved words are *not* excluded
here: Lean lexes an identifier greedily across dots and only treats the resulting token as a keyword
when the whole token matches one, so `Prop.partialOrder` is an ordinary identifier even though
`Prop` alone is a keyword. `refName` applies the reserved check to the full name instead. -/
def isPlainComponent (s : String) : Bool :=
  !s.isEmpty && isIdFirst s.front && (s.drop 1).all isIdRest

/-- True if every component of `n` can be written bare (so `n` needs no escaping). -/
partial def isPlainName : Name → Bool
  | .anonymous => true
  | .str p s => isPlainComponent s && isPlainName p
  | .num _ _ => false

/-- The dotted spelling of `n` with no escaping applied, e.g. `_private.M.0.f`. Hand-rolled rather
than `Name.toString` because that inserts `«…»` per component, which is exactly the decision this
module wants to make for the name as a whole. -/
partial def rawString : Name → String
  | .anonymous => "[anonymous]"
  | .str .anonymous s => s
  | .str p s => rawString p ++ "." ++ s
  | .num .anonymous i => toString i
  | .num p i => rawString p ++ "." ++ toString i

/-- The last component of `n` as a one-component name, e.g. `Foo.Bar.mk ↦ mk`. Used for the
constructor and field names inside an `inductive`/`structure` body, which are written relative to
the type being declared. (Not `Name.getRoot`, which returns the *first* component.) -/
def lastComponent : Name → Name
  | .str _ s => Name.mkSimple s
  | n => n

/-- `n` written as an identifier: bare when every component allows it, otherwise as a single
`«…»`-escaped component holding the whole dotted name.

Escaping the *whole* name (rather than the offending component) is deliberate: `«_private.M.0.f»`
is a one-component name, so it cannot collide with anything Lean generates under `_private`, and
declaration sites and use sites agree as long as both go through this function. -/
def refName (n : Name) : String :=
  let raw := rawString n
  if isPlainName n && !reservedComponents.contains raw then raw else "«" ++ raw ++ "»"

/-- A *constant* name, as both declared and referenced: `refName` under an explicit `_root_.`.

The prefix is not cosmetic. Elaborating `theorem MeasureTheory.Submartingale.foo` puts
`MeasureTheory.Submartingale` and `MeasureTheory` in scope for name resolution, so an unqualified
reference inside it can be captured by a *different* constant of the same short name — for a flat
file whose declarations are spread over many namespaces, that is a live hazard rather than a
theoretical one (`predictablePart` in a `MeasureTheory.…` theorem resolved to Mathlib's
`MeasureTheory.predictablePart` instead of the project's root-level one). `_root_.` makes every
reference absolute, so no enclosing declaration name can capture it. -/
def constName (n : Name) : String := "_root_." ++ refName n

/-! ## Universe levels -/

/-- `some k` if `l` is the literal level `k` (`k` nested `succ`s over `zero`). -/
partial def levelToNat? : Level → Option Nat
  | .zero => some 0
  | .succ l => (levelToNat? l).map (· + 1)
  | _ => none

/-- A level as parseable level syntax. -/
partial def ppLevel (l : Level) : String :=
  match levelToNat? l with
  | some k => toString k
  | none =>
    match l with
    | .zero => "0"
    | .succ l => "(" ++ ppLevel l ++ "+1)"
    | .max a b => "(max " ++ ppLevel a ++ " " ++ ppLevel b ++ ")"
    | .imax a b => "(imax " ++ ppLevel a ++ " " ++ ppLevel b ++ ")"
    | .param n => refName n
    | .mvar _ => "0"   -- cannot occur in a finished declaration

/-- The `.{u, v}` suffix of a declaration id or constant reference (empty when non-polymorphic). -/
def ppLevelParams (us : List Level) : String :=
  if us.isEmpty then "" else ".{" ++ ", ".intercalate (us.map ppLevel) ++ "}"

/-! ## Which constants can be emitted -/

/-- Last components of constants that the `inductive`/`structure` command generates on its own, and
that therefore must never be emitted (declaring one would clash with the generated copy). The
recursor family, constructors, projections and `noConfusion` are recognized by environment
predicates instead; these are the residual spellings Lean exposes no predicate for. -/
def generatedComponents : List String :=
  ["noConfusionType", "ctorIdx", "toCtorIdx", "ind", "below", "ibelow", "brecOn", "binductionOn",
   "rec", "recOn", "casesOn", "sizeOf"]

/-- True if `n` is produced as a side effect of another declaration's command rather than written
by the author, so that emitting it would either clash with the generated copy or be impossible. -/
def isGenerated (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | some (.ctorInfo _) | some (.recInfo _) | some (.quotInfo _) => true
  | _ =>
    env.isProjectionFn n || isAuxRecursor env n || isNoConfusion env n
      || hasConstructorPrefix env n
      || (match n with
          | .str _ s =>
            generatedComponents.contains s || isPrefixWithDigitSuffix "_sizeOf_" s
          | _ => false)

/-- The declaration a generated constant belongs to: the inductive for a constructor or recursor,
otherwise the nearest ancestor name that exists and is not itself generated. A reference to a
generated constant is redirected here, so that emitting the owner regenerates the reference. -/
partial def ownerOf? (env : Environment) (n : Name) : Option Name :=
  match env.find? n with
  | some (.ctorInfo v) => some v.induct
  | some (.recInfo v) => v.all.head?
  | _ => go n.getPrefix
where
  go : Name → Option Name
    | .anonymous => none
    | p => if env.contains p && !isGenerated env p then some p else go p.getPrefix

/-- The constant a reference to `n` should be recorded as: `n` itself when it can be emitted, its
owner when it is generated, `none` when it is not the project's to emit (an imported constant) or
has no emittable owner. -/
def resolveRef (env : Environment) (rootPrefix : Name) (n : Name) : Option Name :=
  if !isProjectLocalConst env rootPrefix n then none
  else if isGenerated env n then
    (ownerOf? env n).filter (isProjectLocalConst env rootPrefix ·)
  else some n

/-! ## Term rendering -/

/-- Rendering state. -/
structure RenderState where
  /-- Constants mentioned so far by the term being printed. -/
  used : Std.HashSet Name := {}
  /-- The inductive types of the `inductive`/`structure` command currently being rendered. Inside
  that command they are *local variables*, not constants: a recursive occurrence must be written
  with the declared name, with no `_root_.` (which only resolves already-declared constants) and no
  explicit universe levels (rejected outright on a local). Parameters are still passed
  explicitly. -/
  selfNames : Std.HashSet Name := {}

/-- Rendering monad: `MetaM` (needed to go under binders and to recognize proofs) plus the state. -/
abbrev RenderM := StateRefT RenderState MetaM

/-- Records a constant reference. -/
def note (n : Name) : RenderM Unit := modify fun s => { s with used := s.used.insert n }

/-- The opening and closing delimiters of a binder group with the given `BinderInfo`. -/
def binderDelims : BinderInfo → String × String
  | .default => ("(", ")")
  | .implicit => ("{", "}")
  | .strictImplicit => ("⦃", "⦄")
  | .instImplicit => ("[", "]")

/-- A fresh binder name for the current depth. Names are unique along any root-to-leaf path (the
local context only grows as we descend), which is all that is needed to avoid shadowing; two
binders in sibling scopes may share a name harmlessly. -/
def freshBinderName : RenderM Name := do
  return Name.mkSimple s!"x_{(← getLCtx).size}"

mutual

/-- A term as parseable Lean syntax.

Every application is `@`-explicit and every constant fully qualified, so the result elaborates with
no notation, no `open`, and no instance synthesis. Proof subterms are replaced by a bare `sorry`,
which is defeq to the original by proof irrelevance.

The `sorry` needs no type ascription: every position a proof can occupy here has a known expected
type, precisely because the output is `@`-explicit and every binder and `let` carries its type.
Ascribing would defeat the purpose — a proof's *statement* is often large too, and the ascription
would drag the statement's constants into the dependency closure for no benefit. -/
partial def ppTerm (e : Expr) : RenderM String := do
  match e with
  -- Types and literals are never proofs, so the (expensive) `isProof` check is skipped for them.
  | .sort l => return "(Sort " ++ ppLevel l ++ ")"
  | .lit (.natVal k) => return s!"(nat_lit {k})"
  | .lit (.strVal s) => return s.quote
  | .forallE .. => ppCore e
  | _ => if ← isProof e then return "sorry" else ppCore e

/-- `ppTerm` without the proof-erasure check (which `ppTerm` has already made). -/
partial def ppCore (e : Expr) : RenderM String := do
  match e with
  | .bvar _ => return "sorry"          -- a loose bvar cannot occur: binders are instantiated
  | .mvar _ => return "sorry"          -- cannot occur in a finished declaration
  | .fvar id => return refName (← id.getUserName)
  | .sort l => return "(Sort " ++ ppLevel l ++ ")"
  | .lit (.natVal k) => return s!"(nat_lit {k})"
  | .lit (.strVal s) => return s.quote
  | .mdata _ b => ppTerm b
  | .proj _ i b => return "(" ++ (← ppTerm b) ++ ")." ++ toString (i + 1)
  | .const n us =>
    if (← get).selfNames.contains n then
      return "@" ++ refName n            -- a local of the enclosing `inductive` command
    else
      note n
      return "@" ++ constName n ++ ppLevelParams us
  | .app .. =>
    let mut out ← ppTerm e.getAppFn
    for a in e.getAppArgs do
      out := out ++ " " ++ (← ppTerm a)
    return "(" ++ out ++ ")"
  | .lam _ t b bi =>
    let nm ← freshBinderName
    let ts ← ppTerm t
    withLocalDecl nm bi t fun x => do
      let (o, c) := binderDelims bi
      return "(fun " ++ o ++ refName nm ++ " : " ++ ts ++ c ++ " => "
        ++ (← ppTerm (b.instantiate1 x)) ++ ")"
  | .forallE _ t b bi =>
    let nm ← freshBinderName
    let ts ← ppTerm t
    withLocalDecl nm bi t fun x => do
      let (o, c) := binderDelims bi
      return "(" ++ o ++ refName nm ++ " : " ++ ts ++ c ++ " → "
        ++ (← ppTerm (b.instantiate1 x)) ++ ")"
  | .letE _ t v b _ =>
    let nm ← freshBinderName
    let ts ← ppTerm t
    let vs ← ppTerm v
    withLetDecl nm t v fun x => do
      return "(let " ++ refName nm ++ " : " ++ ts ++ " := " ++ vs ++ "; "
        ++ (← ppTerm (b.instantiate1 x)) ++ ")"

end

/-- Instantiates the leading `∀`-binders of `ty` with local hypotheses named by `mkName`, stopping
after `count` of them (or at the first non-`∀` when `count` is `none`), and runs `k` on the
resulting free variables and the remaining body.

A hand-rolled telescope rather than `forallBoundedTelescope` because the binder names matter here:
they are what `ppTerm` prints for the corresponding `.fvar`, and the names carried by the type are
frequently inaccessible (`inst✝`) or duplicated. -/
partial def withNamedBinders {α : Type} (ty : Expr) (count : Option Nat) (mkName : Nat → Name)
    (k : Array Expr → Expr → RenderM α) : RenderM α :=
  go ty #[]
where
  go (ty : Expr) (acc : Array Expr) : RenderM α := do
    if count == some acc.size then k acc ty
    else match ty with
      | .forallE _ t b bi =>
        withLocalDecl (mkName acc.size) bi t fun x => go (b.instantiate1 x) (acc.push x)
      | _ => k acc ty

/-- A binder group `(x_0 : T)` / `{x_0 : T}` / … for the local hypothesis `x`. -/
def ppBinderOf (x : Expr) : RenderM String := do
  let d ← x.fvarId!.getDecl
  let (o, c) := binderDelims d.binderInfo
  return o ++ refName d.userName ++ " : " ++ (← ppTerm d.type) ++ c

/-! ## Declaration rendering -/

/-- A rendered declaration: the command to emit, and the project-local constants it references
(already resolved through `resolveRef`, so every entry is itself emittable). -/
structure Rendered where
  cmd : String
  refs : Array Name
deriving Inhabited

/-- The declaration id with its universe binders, e.g. `MyLib.foo.{u, v}`. -/
def ppDeclId (n : Name) (levelParams : List Name) : String :=
  constName n ++ ppLevelParams (levelParams.map Level.param)

/-- Renders an `inductive`/`structure`/`class` command for `v`.

Structures are emitted as `structure` rather than `inductive` so that projections — and the
`Expr.proj` nodes that print as `x.1` — keep working, and a structure that is a class is emitted as
`class`: `@`-explicit applications never need instance synthesis, but an instance-implicit *binder*
`[x : C α]` is still rejected outright when `C` is not registered as a class. -/
def renderInductive (env : Environment) (n : Name) (v : InductiveVal) : RenderM String := do
  modify fun s => { s with selfNames := v.all.foldl (·.insert ·) s.selfNames }
  let isStruct := isStructure env n && v.ctors.length == 1
  let keyword := if isStruct then (if isClass env n then "class" else "structure") else "inductive"
  let fields := if isStruct then getStructureFields env n else #[]
  let paramName (i : Nat) : Name := Name.mkSimple s!"p_{i}"
  withNamedBinders v.type (some v.numParams) paramName fun params rest => do
    let paramStrs ← params.mapM ppBinderOf
    let paramClause := if paramStrs.isEmpty then "" else " " ++ " ".intercalate paramStrs.toList
    let restStr ← ppTerm rest
    let header := keyword ++ " " ++ ppDeclId n v.levelParams ++ paramClause ++ " : " ++ restStr
      ++ " where"
    if isStruct then
      let ctorName := v.ctors.head!
      let some ctorInfo := env.find? ctorName | throwError "missing constructor {ctorName}"
      let ctorTy ← instantiateForall ctorInfo.type params
      -- Field binders are named by their real projection names: those names *are* the projections
      -- the rest of the file refers to, and later field types refer back to earlier fields.
      withNamedBinders ctorTy none (fun i => fields[i]!) fun fs _ => do
        let fieldStrs ← fs.mapM ppBinderOf
        let ctorClause := "  " ++ refName (lastComponent ctorName) ++ " ::"
        return String.intercalate "\n" (header :: ctorClause :: fieldStrs.toList.map ("  " ++ ·))
    else
      let mut lines := [header]
      for ctorName in v.ctors do
        let some ctorInfo := env.find? ctorName | continue
        let ctorTy ← instantiateForall ctorInfo.type params
        lines := lines ++ [s!"  | {refName (lastComponent ctorName)} : " ++ (← ppTerm ctorTy)]
      return String.intercalate "\n" lines

/-- Size in characters past which a definition's rendered value is dropped and the definition is
emitted as an `axiom` instead.

`Expr` is a DAG, but printed syntax is a tree: a value with heavily shared subterms expands by
orders of magnitude. Uncapped, one brownian-motion target rendered to 34 MB and was still
elaborating after 45 minutes. Dropping the value costs the ability to unfold that definition, which
matters only for kernel defeq checks — a far better trade for a tier whose whole purpose is to
produce a file that compiles. -/
def maxDefValueSize : Nat := 100000

/-- Renders `n` as a single self-contained command, or `none` if it is not something this tier
emits (a generated constant, or one outside the project).

Theorems and axioms become `sorry`/`axiom`; definitions keep their (proof-erased) value, because
downstream typechecking may need to unfold them, unless it exceeds `maxDefValueSize`;
`partial`/`unsafe` definitions and `opaque`s become `axiom`, which needs no inhabitant and no
compiler support. -/
def renderConst (env : Environment) (rootPrefix : Name) (n : Name) : MetaM (Option Rendered) := do
  let some info := env.find? n | return none
  if isGenerated env n then return none
  let render (act : RenderM String) : MetaM (Option Rendered) := do
    let (cmd, st) ← act.run {}
    let refs := st.used.toArray.filterMap fun m =>
      if m == n then none else resolveRef env rootPrefix m
    return some { cmd, refs }
  -- An `axiom` carrying only the type. Rendered from a fresh state, so the discarded value's
  -- constants stay out of the dependency closure.
  let asAxiom (ty : Expr) (levelParams : List Name) (note : String) : MetaM (Option Rendered) :=
    render do return note ++ s!"axiom {ppDeclId n levelParams} : " ++ (← ppTerm ty)
  match info with
  | .thmInfo v =>
    render do return s!"theorem {ppDeclId n v.levelParams} : " ++ (← ppTerm v.type) ++ " := sorry"
  | .axiomInfo v => asAxiom v.type v.levelParams ""
  | .opaqueInfo v => asAxiom v.type v.levelParams ""
  | .defnInfo v =>
    if v.safety != .safe then
      asAxiom v.type v.levelParams "-- `partial`/`unsafe` definition; value not reproduced.\n"
    else
      let some r ← render do
          return s!"def {ppDeclId n v.levelParams} : " ++ (← ppTerm v.type) ++ " :=\n  "
            ++ (← ppTerm v.value)
        | return none
      if r.cmd.length ≤ maxDefValueSize then return some r
      else
        asAxiom v.type v.levelParams
          s!"-- Value dropped ({r.cmd.length} chars fully explicit); see `maxDefValueSize`.\n"
  | .inductInfo v =>
    -- A mutual inductive family has to be declared by a single `mutual … end` block. The first
    -- member of `v.all` carries that whole block; the others render to nothing and simply depend
    -- on it, so pulling any member into a closure emits the family exactly once.
    match v.all with
    | [_] => render (renderInductive env n v)
    | all =>
      let some head := all.head? | return none
      if n != head then
        return some { cmd := "", refs := #[head] }
      else
        render do
          let mut blocks : Array String := #[]
          for m in all do
            let some (.inductInfo mv) := env.find? m | continue
            blocks := blocks.push (← renderInductive env m mv)
          return "mutual\n" ++ String.intercalate "\n" blocks.toList ++ "\nend"
  | .ctorInfo _ | .recInfo _ | .quotInfo _ => return none

/-! ## Driver -/

/-- Renders every emittable project-local constant once. A constant whose rendering throws (a
malformed or unsupported shape) is dropped with a warning rather than aborting the run; a target
that depends on it will fail its compile check, which is the signal we want. -/
def renderAll (env : Environment) (rootPrefix : Name) :
    MetaM (Std.HashMap Name Rendered × Array (Name × String)) := do
  let mut out : Std.HashMap Name Rendered := {}
  let mut failures : Array (Name × String) := #[]
  for (name, _, _) in projectConstants env rootPrefix do
    if isGenerated env name then continue
    match ← (try
        (·.map Sum.inl) <$> renderConst env rootPrefix name
      catch ex => return some (Sum.inr (← ex.toMessageData.toString))) with
    | some (.inl r) => out := out.insert name r
    | some (.inr msg) => failures := failures.push (name, msg)
    | none => pure ()
  return (out, failures)

/-- The file header: the external import frontier plus the options the flat form needs.

`autoImplicit` off turns any name that failed to be emitted into a hard error rather than a silently
auto-bound variable; `noncomputable section` removes every compiler-generated complaint about
definitions whose values contain `sorry`, which is most of them. `checkBinderAnnotations` off is
the backstop for an instance-implicit binder whose class this tier could not re-register (the
applications are `@`-explicit, so nothing is ever synthesized from such a binder anyway). -/
def fileHeader (env : Environment) (rootPrefix : Name) (target : Name) (modules : Array Name)
    (count : Nat) : String :=
  let imports := externalImports env rootPrefix modules
  let importBlock :=
    if imports.isEmpty then "import Mathlib\n"
    else String.join (imports.toList.map (fun i => s!"import {i}\n"))
  importBlock ++ s!"
/-! # Flat standalone extraction for `{target}`
Rendered from the compiled environment, not from source: names are fully qualified, applications
are `@`-explicit, and proofs are `sorry`. {count} declarations.
Auto-generated by Referee (fallback extraction). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.all false
set_option checkBinderAnnotations false
set_option warn.classDefReducibility false

noncomputable section

"

/-- Assembles the flat standalone file for `target` from the pre-rendered declarations. `root` is
the name whose closure is emitted — the same as `target` except when `target` is auto-generated, in
which case it is the declaration that generates it. -/
def assembleTarget (env : Environment) (rootPrefix : Name) (rendered : Std.HashMap Name Rendered)
    (refsMap : Std.HashMap Name (Array Name)) (target root : Name) : String := Id.run do
  -- `topologicalClosure` emits each name after everything it references (depth-first post-order),
  -- and tolerates the cycles that mutual blocks and recursive structures introduce.
  let order := (topologicalClosure refsMap #[root]).filter rendered.contains
  let modules := order.filterMap (moduleNameOf env ·)
  let mut out := fileHeader env rootPrefix target modules order.size
  unless root == target do
    out := out ++ s!"-- `{target}` is generated by `{root}`, emitted below.\n\n"
  for n in order do
    -- An empty command is a non-head member of a mutual block: the block itself is emitted by the
    -- head, which the closure already contains.
    if let some r := rendered.get? n then
      unless r.cmd.isEmpty do out := out ++ r.cmd ++ "\n\n"
  return out ++ "end\n"

/-- Writes a flat standalone `<anchorId>.lean` file for every declaration in `decls` into `dir`.
Every project constant is rendered once up front; each target is then a topological filter over
that table. Returns the number of files written. -/
def writeAllFlatExtractions (env : Environment) (rootPrefix : Name) (decls : Array DeclInfo)
    (dir : System.FilePath) : IO Nat := do
  let ctx : Core.Context :=
    { fileName := "<flat-extract>", fileMap := default, maxHeartbeats := 0 }
  let ((rendered, failures), _) ←
    ((renderAll env rootPrefix).run' {} {}).toIO ctx { env := env }
  unless failures.isEmpty do
    IO.eprintln s!"flat extraction: {failures.size} declaration(s) could not be rendered"
    for (n, msg) in failures.toList.take 10 do
      IO.eprintln s!"  {n}: {msg.replace "\n" " " |>.take 160}"
  let refsMap : Std.HashMap Name (Array Name) :=
    rendered.fold (fun m n r => m.insert n r.refs) {}
  IO.FS.createDirAll dir
  let mut written := 0
  let mut skipped : Array Name := #[]
  for decl in decls do
    -- A target this tier does not emit is auto-generated (the primary pipeline exposes a few
    -- `.below`/`.brecOn` helpers); emit the closure of the declaration that generates it instead,
    -- so every target still gets a file.
    let root? := if rendered.contains decl.name then some decl.name
      else (resolveRef env rootPrefix decl.name).filter rendered.contains
    let some root := root? | skipped := skipped.push decl.name; continue
    IO.FS.writeFile (dir / s!"{anchorIdOf decl.name}.lean")
      (assembleTarget env rootPrefix rendered refsMap decl.name root)
    written := written + 1
  unless skipped.isEmpty do
    IO.eprintln s!"flat extraction: no file for {skipped.size} target(s), e.g. {skipped[0]!}"
  return written

end Referee.Flat
