/-
Copyright (c) 2024 Geoffrey Irving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Irving
-/
module

public import Aesop
public import Mathlib.Tactic.Bound.Init
public import Mathlib.Tactic.Linarith.Frontend
public import Qq

/-!
# The `bound` attribute

Any lemma tagged with `@[bound]` is registered as an apply rule for the `bound` tactic, by
converting it to either `norm apply` or `safe apply <priority>`.  The classification is based
on the number and types of the lemma's hypotheses.
-/

public meta section

open Lean (MetaM)
open Qq

namespace Mathlib.Tactic.Bound

initialize Lean.registerTraceClass `bound.attribute

variable {u : Lean.Level} {α : Q(Type u)}

/-- Check if an expression is zero -/
def isZero (e : Q($α)) : MetaM Bool :=
  match e with
  | ~q(@OfNat.ofNat.{u} _ (nat_lit 0) $i) => return true
  | _ => return false

/-- Map the arguments of an inequality expression to a score -/
def ineqPriority (a b : Q($α)) : MetaM Nat := do
  return if (← isZero a) || (← isZero b) then 1 else 10

/-- Map a hypothesis type to a score -/
partial def hypPriority (hyp : Q(Prop)) : MetaM Nat := do
  match hyp with
    -- Conjunctions add scores
    | ~q($a ∧ $b) => pure <| (← hypPriority a) + (← hypPriority b)
    -- Guessing (disjunction) gets a big penalty
    | ~q($a ∨ $b) => pure <| 100 + (← hypPriority a) + (← hypPriority b)
    -- Inequalities get score 1 if they contain zero, 10 otherwise
    | ~q(@LE.le _ $i $a $b) => ineqPriority a b
    | ~q(@LT.lt _ $i $a $b) => ineqPriority a b
    | ~q(@GE.ge _ $i $b $a) => ineqPriority a b
    | ~q(@GT.gt _ $i $b $a) => ineqPriority a b
    -- Assume anything else is non-relevant
    | _ => pure 0

/-- Map a type to a score -/
def typePriority (decl : Lean.Name) (type : Lean.Expr) : MetaM Nat :=
  Lean.Meta.forallTelescope type fun xs t ↦ do
    checkResult t
    xs.foldlM (fun (t : Nat) x ↦ do return t + (← argPriority x)) 0
where
  /-- Score the type of argument `x` -/
  argPriority (x : Lean.Expr) : MetaM Nat := do
    hypPriority (← Lean.Meta.inferType x)
  /-- Insist that our conclusion is an inequality -/
  checkResult (t : Q(Prop)) : MetaM Unit := do match t with
    | ~q(@LE.le _ $i $a $b) => return ()
    | ~q(@LT.lt _ $i $a $b) => return ()
    | ~q(@GE.ge _ $i $b $a) => return ()
    | ~q(@GT.gt _ $i $b $a) => return ()
    | _ => throwError (f!"`{decl}` has invalid type `{type}` as a 'bound' lemma: \
                          it should be an inequality")

/-- Map a theorem decl to a score (0 means `norm apply`, `0 <` means `safe apply`) -/
def declPriority (decl : Lean.Name) : Lean.MetaM Nat := do
  match (← Lean.getEnv).find? decl with
    | some info => do
        typePriority decl info.type
    | none => throwError "unknown declaration {decl}"

/-- Map a score to either `norm apply` or `safe apply <priority>` -/
def scoreToConfig (decl : Lean.Name) (score : Nat) : Aesop.Frontend.RuleConfig :=
  let (phase, priority) := match score with
    | 0 => (Aesop.PhaseName.norm, 0)  -- No hypotheses: this rule closes the goal immediately
    | s => (Aesop.PhaseName.safe, s)
  { term? := some (Lean.mkIdent decl)
    phase? := phase
    priority? := some (Aesop.Frontend.Priority.int priority)
    builder? := some (.regular .apply)
    builderOptions := {}
    ruleSets := ⟨#[`Bound]⟩ }

/-- Register a lemma as an `apply` rule for the `bound` tactic.

A lemma is appropriate for `bound` if it proves an inequality using structurally simpler
inequalities, "recursing" on the structure of the expressions involved, assuming positivity or
nonnegativity where useful. Examples include
1. `gcongr`-like inequalities over `<` and `≤` such as `f x ≤ f y` where `f` is monotone (note that
   `gcongr` supports other relations).
2. `mul_le_mul` which proves `a * b ≤ c * d` from `a ≤ c ∧ b ≤ d ∧ 0 ≤ b ∧ 0 ≤ c`
3. Positivity or nonnegativity inequalities such as `sub_nonneg`: `a ≤ b → 0 ≤ b - a`
4. Inequalities involving `1` such as `one_le_div` or `Real.one_le_exp`
5. Disjunctions where the natural recursion branches, such as `a ^ n ≤ a ^ m` when the inequality
   for `n,m` depends on whether `1 ≤ a ∨ a ≤ 1`.

Each `@[bound]` lemma is assigned a score based on the number and complexity of its hypotheses,
and the `aesop` implementation chooses lemmas with lower scores first:
1. Inequality hypotheses involving `0` add 1 to the score.
2. General inequalities add `10`.
3. Disjunctions `a ∨ b` add `100` plus the sum of the scores of `a` and `b`.

The functionality of `bound` overlaps with `positivity` and `gcongr`, but can jump back and forth
between `0 ≤ x` and `x ≤ y`-type inequalities.  For example, `bound` proves
  `0 ≤ c → b ≤ a → 0 ≤ a * c - b * c`
by turning the goal into `b * c ≤ a * c`, then using `mul_le_mul_of_nonneg_right`.  `bound` also
uses specialized lemmas for goals of the form `1 ≤ x, 1 < x, x ≤ 1, x < 1`.

See also `@[bound_forward]` which marks a lemma as a forward rule for `bound`: these lemmas are
applied to hypotheses to extract inequalities (e.g. `HasPowerSeriesOnBall.r_pos`). -/
@[attribute] def boundAttr : Lean.AttributeImpl where
  name := `bound
  descr := "Register a theorem as an apply rule for the `bound` tactic."
  applicationTime := .afterCompilation
  add := fun decl stx attrKind => Lean.withRef stx do
    let score ← Aesop.runTermElabMAsCoreM <| declPriority decl
    trace[bound.attribute] "'{decl}' has score '{score}'"
    let context ← Aesop.runMetaMAsCoreM Aesop.ElabM.Context.forAdditionalGlobalRules
    let (rule, ruleSets) ← Aesop.runTermElabMAsCoreM <|
      (scoreToConfig decl score).buildGlobalRule.run context
    for ruleSet in ruleSets do
      Aesop.Frontend.addGlobalRule ruleSet rule attrKind (checkNotExists := true)
  erase := fun decl =>
    let ruleFilter := { name := decl, scope := .global, builders := #[], phases := #[] }
    Aesop.Frontend.eraseGlobalRules Aesop.RuleSetNameFilter.all ruleFilter (checkExists := true)

/-- Attribute for `forward` rules for the `bound` tactic.

`@[bound_forward]` lemmas should produce inequalities given other hypotheses that might be in the
context. A typical example is exposing an inequality field of a structure, such as
`HasPowerSeriesOnBall.r_pos`. -/
macro "bound_forward" : attr =>
  `(attr|aesop safe forward (rule_sets := [$(Lean.mkIdent `Bound):ident]))

/-!
### Apply rules for `bound`

Most `bound` lemmas are registered in-place where the lemma is declared. These are the basic
arithmetic/order lemmas which would create circular import issues if registered at their
declaration sites.
-/

lemma Nat.cast_pos_of_pos {R : Type} [Semiring R] [PartialOrder R] [IsOrderedRing R] [Nontrivial R]
    {n : ℕ} : 0 < n → 0 < (n : R) :=
  Nat.cast_pos.mpr

lemma Nat.one_le_cast_of_le {α : Type} [AddCommMonoidWithOne α] [PartialOrder α]
    [AddLeftMono α] [ZeroLEOneClass α]
    [CharZero α] {n : ℕ} : 1 ≤ n → 1 ≤ (n : α) :=
  Nat.one_le_cast.mpr

-- Reflexivity
attribute [bound] le_refl

-- 0 ≤, 0 <
attribute [bound] sq_nonneg Nat.cast_nonneg abs_nonneg Nat.zero_lt_succ pow_pos pow_nonneg
  sub_nonneg_of_le sub_pos_of_lt inv_nonneg_of_nonneg inv_pos_of_pos tsub_pos_of_lt mul_pos
  mul_nonneg div_pos div_nonneg add_nonneg

-- 1 ≤, ≤ 1
attribute [bound] Nat.one_le_cast_of_le one_le_mul_of_one_le_of_one_le

-- ≤
attribute [bound] le_abs_self neg_abs_le neg_le_neg tsub_le_tsub_right mul_le_mul_of_nonneg_left
  mul_le_mul_of_nonneg_right le_add_of_nonneg_right le_add_of_nonneg_left le_mul_of_one_le_right
  mul_le_of_le_one_right sub_le_sub add_le_add mul_le_mul

-- <
attribute [bound] Nat.cast_pos_of_pos neg_lt_neg sub_lt_sub_left sub_lt_sub_right add_lt_add_left
  add_lt_add_right mul_lt_mul_of_pos_left mul_lt_mul_of_pos_right

-- min and max
attribute [bound] min_le_right min_le_left le_max_left le_max_right le_min max_le lt_min max_lt

-- Memorize a few constants to avoid going to `norm_num`
attribute [bound] zero_le_one zero_lt_one zero_le_two zero_lt_two

/-!
### Forward rules for `bound`
-/

-- Bound applies `le_of_lt` to all hypotheses
attribute [bound_forward] le_of_lt

end Mathlib.Tactic.Bound
