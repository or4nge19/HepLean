/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import Batteries.Lean.HashSet
import Lean
import Mathlib.Lean.Expr.Basic
import Mathlib.Lean.CoreM
import HepLean.Meta.Informal
import ImportGraph.RequiredModules
/-!

# Extracting information about informal definitions and lemmas

-/

open Lean System Meta

def getConst (imp : Import) : IO (Array (Import × ConstantInfo)) := do
  let mFile ← findOLean imp.module
  let (modData, _) ← readModuleData mFile
  pure (modData.constants.map (fun c => (imp, c)))

def getLineNumber (c : Name) : MetaM Nat := do
  match ← findDeclarationRanges? c  with
  | some decl => pure decl.range.pos.line
  | none => panic! s!"{c} is a declaration without position"

def getModule (c : Name) : MetaM Name := do
  match Lean.Environment.getModuleFor? (← getEnv) c with
  | some mod => pure mod
  | none => panic! s!"{c} is a declaration without position"

def depToString (d : Name) : MetaM String := do
  let lineNo ← getLineNumber d
  let mod ← getModule d
  pure s!"    * {d}: ./{mod.toString.replace "." "/" ++ ".lean"}:{lineNo}"

def depToWebString (d : Name) : MetaM String := do
  let lineNo ← getLineNumber d
  let mod ← getModule d
  let webPath := "https://github.com/HEPLean/HepLean/blob/master/"++
    (mod.toString.replace "." "/") ++ ".lean"
  pure s!"    * [{d}]({webPath}#L{lineNo})"

unsafe def informalLemmaToString (c : Import × ConstantInfo) : MetaM String := do
  let lineNo ← getLineNumber c.2.name
  let informalLemma ←
    match c.2 with
    | ConstantInfo.defnInfo c =>
        Lean.Meta.evalExpr' InformalLemma ``InformalLemma c.value
    | _ => panic! "This should not happen"
  let dep ← informalLemma.dependencies.mapM fun d => depToString d
  pure s!"
Informal lemma: {informalLemma.name}
- ./{c.1.module.toString.replace "." "/" ++ ".lean"}:{lineNo}
- Math description: {informalLemma.math}
- Physics description: {informalLemma.physics}
- Proof description: {informalLemma.proof}
- References: {informalLemma.ref}
- Dependencies:\n{String.intercalate "\n" dep}"

unsafe def informalLemmaToWebString (c : Import × ConstantInfo) : MetaM String := do
  let lineNo ← getLineNumber c.2.name
  let informalLemma ←
    match c.2 with
    | ConstantInfo.defnInfo c =>
        Lean.Meta.evalExpr' InformalLemma ``InformalLemma c.value
    | _ => panic! "This should not happen"
  let dep ← informalLemma.dependencies.mapM fun d => depToWebString d
  let webPath := "https://github.com/HEPLean/HepLean/blob/master/"++
    (c.1.module.toString.replace "." "/") ++ ".lean"
  pure s!"
**Informal lemma**: [{informalLemma.name}]({webPath}#L{lineNo}) :=
  *{informalLemma.math}*
- Physics description: {informalLemma.physics}
- Proof description: {informalLemma.proof}
- References: {informalLemma.ref}
- Dependencies:\n{String.intercalate "\n" dep}"

unsafe def informalDefToString (c : Import × ConstantInfo) : MetaM String := do
  let lineNo ← getLineNumber c.2.name
  let informalDef ←
    match c.2 with
    | ConstantInfo.defnInfo c =>
        Lean.Meta.evalExpr' InformalDefinition ``InformalDefinition c.value
    | _ => panic! "This should not happen"
  let dep ← informalDef.dependencies.mapM fun d => depToString d
  pure s!"
Informal def: {informalDef.name}
- ./{c.1.module.toString.replace "." "/" ++ ".lean"}:{lineNo}
- Math description: {informalDef.math}
- Physics description: {informalDef.physics}
- References: {informalDef.ref}
- Dependencies:\n{String.intercalate "\n" dep}"

unsafe def informalDefToWebString (c : Import × ConstantInfo) : MetaM String := do
  let lineNo ← getLineNumber c.2.name
  let informalDef ←
    match c.2 with
    | ConstantInfo.defnInfo c =>
        Lean.Meta.evalExpr' InformalDefinition ``InformalDefinition c.value
    | _ => panic! "This should not happen"
  let dep ← informalDef.dependencies.mapM fun d => depToWebString d
  let webPath := "https://github.com/HEPLean/HepLean/blob/master/"++
    (c.1.module.toString.replace "." "/") ++ ".lean"
  pure s!"
**Informal def**: [{informalDef.name}]({webPath}#L{lineNo}) :=
  *{informalDef.math}*
- Physics description: {informalDef.physics}
- References: {informalDef.ref}
- Dependencies:\n{String.intercalate "\n" dep}"

unsafe def informalToString (c : Import × ConstantInfo) : MetaM String := do
  if Informal.isInformalLemma c.2 then
    informalLemmaToString c
  else if Informal.isInformalDef c.2 then
    informalDefToString c
  else
    pure ""

unsafe def informalToWebString (c : Import × ConstantInfo) : MetaM String := do
  if Informal.isInformalLemma c.2 then
    informalLemmaToWebString c
  else if Informal.isInformalDef c.2 then
    informalDefToWebString c
  else
    pure ""

def informalFileHeader : String := s!"
# Informal definitions and lemmas


"

unsafe def importToString (i : Import) : MetaM String := do
  let constants ← getConst i
  let constants := constants.filter (fun c => ¬ Lean.Name.isInternalDetail c.2.name)
  let informalConst := constants.filter fun c => Informal.isInformal c.2
  let informalConstLineNo ← informalConst.mapM fun c => getLineNumber c.2.name
  let informalConstWithLineNo := informalConst.zip informalConstLineNo
  let informalConstWithLineNoSort := informalConstWithLineNo.qsort (fun a b => a.2 < b.2)
  let informalConst := informalConstWithLineNoSort.map (fun c => c.1)
  let informalPrint ← (informalConst.mapM informalToString).run'
  if informalPrint.isEmpty then
    pure ""
  else
    pure ("\n\n" ++ i.module.toString ++ "\n" ++ String.intercalate "\n\n" informalPrint.toList)

unsafe def importToWebString (i : Import) : MetaM String := do
  let constants ← getConst i
  let constants := constants.filter (fun c => ¬ Lean.Name.isInternalDetail c.2.name)
  let informalConst := constants.filter fun c => Informal.isInformal c.2
  let informalConstLineNo ← informalConst.mapM fun c => getLineNumber c.2.name
  let informalConstWithLineNo := informalConst.zip informalConstLineNo
  let informalConstWithLineNoSort := informalConstWithLineNo.qsort (fun a b => a.2 < b.2)
  let informalConst := informalConstWithLineNoSort.map (fun c => c.1)
  let informalPrint ← (informalConst.mapM informalToWebString).run'
  if informalPrint.isEmpty then
    pure ""
  else
    pure ("\n\n## " ++ i.module.toString ++ "\n" ++ String.intercalate "\n\n" informalPrint.toList)
unsafe def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let mods : Name := `HepLean
  let imp : Import := {module := mods}
  let mFile ← findOLean imp.module
  unless (← mFile.pathExists) do
        throw <| IO.userError s!"object file '{mFile}' of module {imp.module} does not exist"
  let (hepLeanMod, _) ← readModuleData mFile
  let imports := hepLeanMod.imports.filter (fun c => c.module ≠ `Init)
  let importString ← CoreM.withImportModules #[`HepLean] (imports.mapM importToString).run'
  IO.println (String.intercalate "" importString.toList)
  /- Writing out informal file. -/
  let fileOut : System.FilePath := {toString := "./docs/Informal.md"}
  if "mkFile" ∈ args then
    let importWebString ← CoreM.withImportModules #[`HepLean] (imports.mapM importToWebString).run'
    let out := String.intercalate "\n" importWebString.toList
    IO.println (s!"Informal file made.")
    IO.FS.writeFile fileOut (informalFileHeader ++ out)
