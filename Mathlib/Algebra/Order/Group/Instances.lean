/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl

! This file was ported from Lean 3 source module algebra.order.group.instances
! leanprover-community/mathlib commit a95b16cbade0f938fc24abd05412bde1e84bab9b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Monoid.OrderDual

/-!
# Additional instances for ordered commutative groups.

-/


variable {α : Type _}

@[to_additive]
instance [OrderedCommGroup α] : OrderedCommGroup αᵒᵈ :=
  { OrderDual.instOrderedCommMonoidOrderDual, instGroupOrderDual with }
#align order_dual.ordered_comm_group instOrderedCommGroupOrderDual
#align order_dual.ordered_add_comm_group instOrderedAddCommGroupOrderDual

@[to_additive]
instance [LinearOrderedCommGroup α] : LinearOrderedCommGroup αᵒᵈ :=
  { instOrderedCommGroupOrderDual, OrderDual.instLinearOrderOrderDual α with }
