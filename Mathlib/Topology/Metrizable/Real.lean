/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Order.Real
import Mathlib.Data.ENNReal.Inv
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Topology.Order.T5
import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# `ENNReal` is metrizable

## Implementation details

This file currently only contains results on `ENNReal` but is named `Real.lean`
to make it clear we can accept more `(E)(NN)Real` results.
-/

@[expose] public section

namespace ENNReal

open NNReal TopologicalSpace

instance : MetrizableSpace ENNReal :=
  orderIsoUnitIntervalBirational.toHomeomorph.isEmbedding.metrizableSpace

end ENNReal
