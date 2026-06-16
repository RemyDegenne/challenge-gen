import LMLExposition.Extract

/-!
# Tests for `LMLExposition.Extract`

Extraction renders declarations from the elaborated environment, which needs an `Environment`;
that path is exercised end-to-end against a real project. The pure helper unit tests that existed
here (`emitOrder`) were removed when `Extract.lean` was rewritten to derive declaration order
directly from the environment's module graph rather than a standalone topological sort.
-/
