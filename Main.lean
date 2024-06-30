import «CyclicFormulas»

open Std.Format Formula Program

-- def formula_in := dim (test (prop 3) ∪∪ star (atom 0)) <| and (prop 1) (nprop 2)
-- def dot : IO Unit := do
--   let stdin  ← IO.getStdin
--   let stdout ← IO.getStdout

--   let φ := formula_in
--   let Gφ := ToC2CF' φ

--   stdout.putStr <|
--     s!"digraph \"{reprStr φ}\" \{"
--     ++   "\n\trankdir=LR"
--     ++   "\n\tnode [shape=circle, fixedsize=true];"
--     ++   "\n\tinit [label=\"\", shape=none]"
--     ++ s!"\n\tinit -> {Gφ.vI}"

--   forM (FinEnum.toList Gφ) fun v => stdout.putStr
--     s!"\n\t{v} [color={Gφ.Ω v}, label=\"{Gφ.L v}\"]"

--   forM (FinEnum.toList (Graph.edges Gφ)) fun ⟨(v, w), _⟩ => stdout.putStr
--     s!"\n\t{v} -> {w}"

--   stdout.putStrLn "\n}"

def sim : IO Unit := do
  let stdout ← IO.getStdout
  forM list_formulas fun φ => stdout.putStr s!"{FinEnum.card <| ToC2CF φ} "
  stdout.putStr "\n"

def main := sim

