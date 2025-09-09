/-
Copyright (c) 2025 Jaafar Tanoukhi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jaafar Tanoukhi
-/
import Mathlib.Combinatorics.Digraph.Walk

universe u

namespace Digraph

namespace Walk

variable {V : Type u} [DecidableEq V] (G : Digraph V) (u v : V)

def IsHamiltonian (p : G.Walk u v) : Prop := ∀ a, p.support.count a = 1

end Walk

end Digraph
