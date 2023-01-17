/-
Copyright (c) 2022 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/

import Lean
import Std.Tactic.OpenPrivate

/-!
# Helper functions related to the `simp` tactic.

[TODO] Needs documentation, cleanup, and possibly reunification of `mkSimpContext'` with core.
-/

def Lean.PHashSet.toList [BEq α] [Hashable α] (s : Lean.PHashSet α) : List α :=
  s.1.toList.map (·.1)

namespace Lean

namespace Meta.DiscrTree

partial def Trie.getElements : Trie α s → Array α
  | Trie.node vs children =>
    vs ++ children.concatMap fun (_, child) ↦ child.getElements

def getElements (d : DiscrTree α s) : Array α :=
  d.1.toList.toArray.concatMap fun (_, child) => child.getElements

end Meta.DiscrTree

namespace Meta.Simp
open Elab.Tactic

instance : ToFormat SimpTheorems where
  format s :=
f!"pre:
{s.pre.getElements.toList}
post:
{s.post.getElements.toList}
lemmaNames:
{s.lemmaNames.toList.map (·.key)}
toUnfold: {s.toUnfold.toList}
erased: {s.erased.toList.map (·.key)}
toUnfoldThms: {s.toUnfoldThms.toList}"

def mkEqSymm (e : Expr) (r : Simp.Result) : MetaM Simp.Result :=
  ({ expr := e, proof? := · }) <$>
  match r.proof? with
  | none => pure none
  | some p => some <$> Meta.mkEqSymm p

def mkCast (r : Simp.Result) (e : Expr) : MetaM Expr := do
  mkAppM ``cast #[← r.getProof, e]

/-- Return all propositions in the local context. -/
def getPropHyps : MetaM (Array FVarId) := do
  let mut result := #[]
  for localDecl in (← getLCtx) do
    unless localDecl.isAuxDecl do
      if (← isProp localDecl.type) then
        result := result.push localDecl.fvarId
  return result

export private mkDischargeWrapper from Lean.Elab.Tactic.Simp

-- copied from core
/--
If `ctx == false`, the config argument is assumed to have type `Meta.Simp.Config`,
and `Meta.Simp.ConfigCtx` otherwise.
If `ctx == false`, the `discharge` option must be none
-/
def mkSimpContext' (simpTheorems : SimpTheorems) (stx : Syntax) (eraseLocal : Bool)
    (kind := SimpKind.simp) (ctx := false) (ignoreStarArg : Bool := false) :
    TacticM MkSimpContextResult := do
  if ctx && !stx[2].isNone then
    if kind == SimpKind.simpAll then
      throwError "'simp_all' tactic does not support 'discharger' option"
    if kind == SimpKind.dsimp then
      throwError "'dsimp' tactic does not support 'discharger' option"
  let dischargeWrapper ← mkDischargeWrapper stx[2]
  let simpOnly := !stx[3].isNone
  let simpTheorems ← if simpOnly then
    simpOnlyBuiltins.foldlM (·.addConst ·) {}
  else
    pure simpTheorems
  let congrTheorems ← Meta.getSimpCongrTheorems
  let r ← elabSimpArgs stx[4] (eraseLocal := eraseLocal) (kind := kind) {
    config       := (← elabSimpConfig stx[1] (kind := kind))
    simpTheorems := #[simpTheorems], congrTheorems
  }
  if !r.starArg || ignoreStarArg then
    return { r with dischargeWrapper }
  else
    let mut simpTheorems := r.ctx.simpTheorems
    let hs ← getPropHyps
    for h in hs do
      unless simpTheorems.isErased (.fvar h) do
        simpTheorems ← simpTheorems.addTheorem (.fvar h) (← h.getDecl).toExpr
    return { ctx := { r.ctx with simpTheorems }, dischargeWrapper }

export private checkTypeIsProp shouldPreprocess preprocess mkSimpTheoremCore
  from Lean.Meta.Tactic.Simp.SimpTheorems

/-- Similar to `mkSimpTheoremsFromConst` except that it also returns the names of the generated
lemmas.
Remark: either the length of the arrays is the same,
or the length of the first one is 0 and the length of the second one is 1. -/
def mkSimpTheoremsFromConst' (declName : Name) (post : Bool) (inv : Bool) (prio : Nat) :
  MetaM (Array Name × Array SimpTheorem) := do
  let cinfo ← getConstInfo declName
  let val := mkConst declName (cinfo.levelParams.map mkLevelParam)
  withReducible do
    let type ← inferType val
    checkTypeIsProp type
    if inv || (← shouldPreprocess type) then
      let mut r := #[]
      let mut auxNames := #[]
      for (val, type) in (← preprocess val type inv (isGlobal := true)) do
        let auxName ← mkAuxLemma cinfo.levelParams type val
        auxNames := auxNames.push auxName
        r := r.push <| ← mkSimpTheoremCore (.decl declName)
          (mkConst auxName (cinfo.levelParams.map mkLevelParam)) #[] (mkConst auxName) post prio
      return (auxNames, r)
    else
      return (#[], #[← mkSimpTheoremCore (.decl declName) (mkConst declName <|
        cinfo.levelParams.map mkLevelParam) #[] (mkConst declName) post prio])

/-- Similar to `addSimpTheorem` except that it returns an array of all auto-generated
  simp-theorems. -/
def addSimpTheorem' (ext : SimpExtension) (declName : Name) (post : Bool) (inv : Bool)
  (attrKind : AttributeKind) (prio : Nat) : MetaM (Array Name) := do
  let (auxNames, simpThms) ← mkSimpTheoremsFromConst' declName post inv prio
  for simpThm in simpThms do
    ext.add (SimpEntry.thm simpThm) attrKind
  return auxNames

/-- Similar to `AttributeImpl.add` in `mkSimpAttr` except that it doesn't require syntax,
  and returns an array of all auto-generated lemmas. -/
def addSimpAttr (declName : Name) (ext : SimpExtension) (attrKind : AttributeKind)
  (post : Bool) (prio : Nat) :
    MetaM (Array Name) := do
  let info ← getConstInfo declName
  if (← isProp info.type) then
    addSimpTheorem' ext declName post (inv := false) attrKind prio
  else if info.hasValue then
    if let some eqns ← getEqnsFor? declName then
      let mut auxNames := #[]
      for eqn in eqns do
        -- Is this list is always empty?
        let newAuxNames ← addSimpTheorem' ext eqn post (inv := false) attrKind prio
        auxNames := auxNames ++ newAuxNames
      ext.add (SimpEntry.toUnfoldThms declName eqns) attrKind
      if hasSmartUnfoldingDecl (← getEnv) declName then
        ext.add (SimpEntry.toUnfold declName) attrKind
      return auxNames
    else
      ext.add (SimpEntry.toUnfold declName) attrKind
      return #[]
  else
    throwError "invalid 'simp', it is not a proposition nor a definition (to unfold)"

/-- Similar to `AttributeImpl.add` in `mkSimpAttr` except that it returns an array of all
  auto-generated lemmas. -/
def addSimpAttrFromSyntax (declName : Name) (ext : SimpExtension) (attrKind : AttributeKind)
  (stx : Syntax) : MetaM (Array Name) := do
  let post := if stx[1].isNone then true else stx[1][0].getKind == ``Lean.Parser.Tactic.simpPost
  let prio ← getAttrParamOptPrio stx[2]
  addSimpAttr declName ext attrKind post prio
