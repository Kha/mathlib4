/-
Copyright (c) 2024 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module

public import Mathlib.Tactic.Translate.ToAdditive

/-!
## `@[to_additive]` attributes for basic types
-/

public meta section

set_option linter.privateModule false

namespace Mathlib.Tactic.ToAdditive
open Lean Elab Translate

@[attribute] def toAdditiveDoTranslateAttr : AttributeImpl where
  name := `to_additive_do_translate
  descr := "Auxiliary attribute for `to_additive` stating \
    that the operations on this type should be translated."
  add name _ _ := doTranslateAttr.add name true

@[attribute] def toAdditiveDontTranslateAttr : AttributeImpl where
  name := `to_additive_dont_translate
  descr := "Auxiliary attribute for `to_additive` stating \
    that the operations on this type should not be translated."
  add name _ _ := doTranslateAttr.add name false

@[attribute] def toAdditiveAttr : AttributeImpl where
  name := `to_additive
  descr := "Transport multiplicative to additive"
  add := fun src stx kind ↦ discard do
    addTranslationAttr data src (← elabTranslationAttr src stx) kind
  -- we (presumably) need to run after compilation to properly add the `simp` attribute
  applicationTime := .afterCompilation

end Mathlib.Tactic.ToAdditive

attribute [to_additive_do_translate] Empty PEmpty Unit PUnit
attribute [to_additive_ignore_args 2] Subtype

attribute [to_additive] One
attribute [to_additive existing Zero.toOfNat0] One.toOfNat1
attribute [to_additive existing Zero.ofOfNat0] One.ofOfNat1

attribute [to_additive existing] Inv Mul HMul instHMul Div HDiv instHDiv

attribute [to_additive (reorder := α β) SMul] Pow
attribute [to_additive existing (reorder := α β, 4 5) smul] Pow.pow
attribute [to_additive existing (reorder := α β, pow (1 2))] Pow.mk
attribute [to_additive (reorder := α β)] HPow
attribute [to_additive existing (reorder := α β, 5 6)] HPow.hPow
attribute [to_additive existing (reorder := α β, hPow (1 2))] HPow.mk
attribute [to_additive existing] instHPow
