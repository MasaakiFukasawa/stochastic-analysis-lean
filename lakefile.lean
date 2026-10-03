import Lake
open Lake DSL

package stochasticAnalysis where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "5ed2965256430c3649e86755f9576b54eca72435"

@[default_target]
lean_lib Book where
  srcDir := "src"
  -- Explicit roots keep Mathlib and other dependencies outside this library.
  roots := ((include_str "audit/module-roots.txt").splitOn "\n").toArray.map Lean.Name.mkSimple
