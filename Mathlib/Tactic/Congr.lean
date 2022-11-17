/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Std.Tactic.RCases
import Std.Tactic.Ext
import Lean

/-! # `congr with` tactic, `rcongr` tactic -/

namespace Mathlib.Tactic
open Lean Meta Elab Tactic Std.Tactic

/--
Apply congruence (recursively) to goals of the form `⊢ f as = f bs` and `⊢ HEq (f as) (f bs)`.
* `congr n` controls the depth of the recursive applications.
  This is useful when `congr` is too aggressive in breaking down the goal.
  For example, given `⊢ f (g (x + y)) = f (g (y + x))`,
  `congr` produces the goals `⊢ x = y` and `⊢ y = x`,
  while `congr 2` produces the intended `⊢ x + y = y + x`.
* If, at any point, a subgoal matches a hypothesis then the subgoal will be closed.
* You can use `congr with p (: n)?` to call `ext p (: n)?` to all subgoals generated by `congr`.
  For example, if the goal is `⊢ f '' s = g '' s` then `congr with x` generates the goal
  `x : α ⊢ f x = g x`.
-/
syntax (name := congrWith) "congr" (ppSpace colGt num)?
  " with " (colGt rintroPat)* (" : " num)? : tactic

macro_rules
  | `(tactic| congr $(depth)? with $ps* $[: $n]?) =>
    `(tactic| congr $(depth)? <;> ext $ps* $[: $n]?)

/--
Recursive core of `rcongr`. Calls `ext pats <;> congr` and then itself recursively,
unless `ext pats <;> congr` made no progress.
-/
partial def rcongrCore (g : MVarId) (pats : List (TSyntax `rcasesPat))
    (acc : Array MVarId) : TermElabM (Array MVarId) := do
  let mut acc := acc
  for (g, qs) in ← Ext.extCore g pats (failIfUnchanged := false) do
    let s ← saveState
    let gs ← g.congrN 1000000
    if ← not <$> g.isAssigned <||> gs.anyM fun g' => return (← g'.getType).eqv (← g.getType) then
      s.restore
      acc := acc.push g
    else
      for g in gs do
        acc ← rcongrCore g qs acc
  pure acc

/--
Repeatedly apply `congr` and `ext`, using the given patterns as arguments for `ext`.

There are two ways this tactic stops:
* `congr` fails (makes no progress), after having already applied `ext`.
* `congr` canceled out the last usage of `ext`. In this case, the state is reverted to before
  the `congr` was applied.

For example, when the goal is
```
⊢ (λ x, f x + 3) '' s = (λ x, g x + 3) '' s
```
then `rcongr x` produces the goal
```
x : α ⊢ f x = g x
```
This gives the same result as `congr; ext x; congr`.

In contrast, `congr` would produce
```
⊢ (λ x, f x + 3) = (λ x, g x + 3)
```
and `congr with x` (or `congr; ext x`) would produce
```
x : α ⊢ f x + 3 = g x + 3
```
-/
elab (name := rcongr) "rcongr" ps:(ppSpace colGt rintroPat)* : tactic => do
  let gs ← rcongrCore (← getMainGoal) (RCases.expandRIntroPats ps).toList #[]
  replaceMainGoal gs.toList
