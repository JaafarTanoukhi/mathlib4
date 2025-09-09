/-
Copyright (c) 2025 Jaafar Tanoukhi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jaafar Tanoukhi
-/
import Mathlib.Combinatorics.Digraph.Basic

universe u

namespace Digraph

variable {V : Type u}
variable (G : Digraph V)

inductive Walk : V → V → Type u
  | nil {u : V} : Walk u u
  | cons {u v w : V} (h : G.Adj u v) (p : Walk v w) : Walk u w
  deriving DecidableEq

namespace Walk

def support {u v : V} : G.Walk u v → List V
  | nil => [u]
  | cons _ p => u :: p.support

end Walk

end Digraph
