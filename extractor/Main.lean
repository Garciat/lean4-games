import Lean

open Lean Json ToJson FromJson

structure LeanGameLevel : Type where
  code : String
deriving Lean.ToJson, Lean.FromJson, Inhabited, Repr

abbrev LeanGameWorld := RBMap String LeanGameLevel compare

structure LeanGameFile : Type where
  data : RBMap String LeanGameWorld compare
deriving Lean.ToJson, Lean.FromJson, Inhabited, Repr

def extractGameFiles (inputFile : String) (dest : String) : IO Unit := do
  let text ← IO.FS.readFile inputFile

  let file ←
    match Json.parse text >>= fromJson? (α := LeanGameFile) with
    | Except.ok v => pure v
    | Except.error err =>
      throw $ IO.userError s!"Error: {err}"

  file.data.forM fun worldName world => do
    world.forM fun levelName level => do
      let code := level.code
      let fileName := s!"{dest}/{worldName}_{levelName}.lean"
      IO.FS.writeFile fileName code
      IO.println s!"Wrote {fileName}"

def main (args : List String) : IO Unit := do
  if _h : args.length = 2 then
    let [inputFile, dest] := args
    extractGameFiles inputFile dest
  else
    throw $ IO.userError "Usage: lean4game <input_file> <dest>"
