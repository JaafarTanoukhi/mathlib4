/-
Copyright (c) 2025 Jaafar Tanoukhi, Rida Hamadani. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jaafar Tanoukhi, Rida Hamadani
-/
import Mathlib.Combinatorics.Digraph.Orientation
import Mathlib.Combinatorics.Digraph.Hamiltonian
import Mathlib.Combinatorics.Digraph.Maps
import Mathlib.Data.Fintype.Option

/-!

# Tournaments

In this file we define tournaments, which are digraphs with exactly one edge between any two
vertices.

We assume that tournaments are loopless.

-/

namespace Digraph

variable (V : Type*) (G : Digraph V)

/--
A tournament is a loopless digraph such that any two vertices have exactly one edge between them.
-/
structure IsTournament : Prop where
  loopless w : ¬ G.Adj w w
  one_edge w v : w ≠ v → (G.Adj w v ↔ ¬ G.Adj v w)

theorem isOrientation_of_isTournament (G : Digraph V) (h : G.IsTournament) :
    G.IsOrientation ⊤ := by
  intro v w
  refine ⟨fun hT ↦ ?_, fun h ↦ ?_⟩
  · rw [h.one_edge w v hT]
    tauto
  · rw [SimpleGraph.top_adj, ne_eq]
    by_contra hc
    rw [hc] at h
    tauto

variable (V : Type*) (G : Digraph V) [DecidableEq V] [Fintype V] [Nonempty V]

lemma comap_isTournament {V V' : Type*} {G : Digraph V'} {f : V ↪ V'} (hG : G.IsTournament) :
  (G.comap f).IsTournament := by
  refine
  { loopless := ?loopless
    one_edge := ?one_edge }
  · intro w
    simpa using hG.loopless (w := f w)
  · intro w v hne
    have hfv_ne : f w ≠ f v := by
      intro h
      exact hne (f.injective h)
    simpa using hG.one_edge (w := f w) (v := f v) hfv_ne


theorem tournament_isTraceable (hG : G.IsTournament) :
   ∃ (a b : V), ∃ (p : G.Walk a b), p.IsHamiltonian := by
  revert G
  expose_names
  revert inst inst_2
  apply Fintype.induction_empty_option (P := fun α _ ↦ [DecidableEq α] → [Nonempty α] →
    ∀ G, IsTournament α G → ∃ a b p, Walk.IsHamiltonian G a b p)
  · intro α β _ f hα _ _ G ht
    classical
    have := Equiv.nonempty_congr f |>.mpr ‹Nonempty _›
    have : G.comap f |>.IsTournament := by exact comap_isTournament (f := f.toEmbedding) ht
    have ⟨a, b, p, h⟩ := hα (G.comap f) this
    use f a, f b
    use p.map (Digraph.Embedding.comap f.toEmbedding G |>.toRelHom)
    sorry
  · aesop
  · intro α _ h _ _ G ht
    by_cases he : Nonempty α; rotate_left
    · use none, none, Walk.nil
      intro a
      have : IsEmpty α := not_nonempty_iff.mp he
      rw [show a = none by exact Unique.uniq _ _]
      simp [Walk.support]
    sorry




end Digraph
