import Downstream.SparseRelabelPreparation
import Downstream.GraphFamilyFacts

set_option autoImplicit false
set_option maxHeartbeats 3000000

/-! The primal graph of the actual tuple-list input, and exact transport of
nonisolation and degree through graph isomorphisms to the expander family. -/
namespace CSPConsequence.SparseGraphTransfer
noncomputable section
open SparseNormalization SparseRelabelPreparation

def primal (p : Input) : SimpleGraph (Fin p.1.length) where
  Adj a b := edgeAt p.2.2 a.val b.val = true
  symm := ⟨fun a b h => (edgeAt_symmetric p.2.2 b.val a.val).trans h⟩
  loopless := ⟨fun a h => by simpa [edgeAt] using h⟩

def neighborsEquiv {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (a : V) : {b // G.Adj a b} ≃ {b // H.Adj (e a) b} where
  toFun b := ⟨e b.val,e.map_adj_iff.mpr b.property⟩
  invFun b := ⟨e.symm b.val,by simpa using e.symm.map_adj_iff.mpr b.property⟩
  left_inv b := by apply Subtype.ext; exact e.symm_apply_apply _
  right_inv b := by apply Subtype.ext; exact e.apply_symm_apply _

theorem degree_eq (p : Input) (a : Fin p.1.length) :
    (semantic p).degree a = Nat.card {b // (primal p).Adj a b} := by
  classical
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
  unfold Instance.degree
  apply congrArg Finset.card
  ext b
  simp only [Finset.mem_filter,Finset.mem_erase,Finset.mem_univ,true_and,and_true]
  change (b ≠ a ∧ edgeAt p.2.2 a.val b.val = true) ↔ edgeAt p.2.2 a.val b.val = true
  constructor
  · exact And.right
  · intro h
    refine ⟨?_,h⟩
    intro he
    subst b
    simp [edgeAt] at h

theorem iso_card (p : Input) (n : ℕ) (e : primal p ≃g GraphFamily.graph n) :
    p.1.length = GraphFamily.familySize n := by
  simpa only [Fintype.card_fin] using Fintype.card_congr e.toEquiv

theorem iso_degree (p : Input) (n : ℕ) (e : primal p ≃g GraphFamily.graph n)
    (a : Fin p.1.length) :
    (semantic p).degree a ≤ Fintype.card OAI.IndependentSetsGames.Foundations.PCP.ExpanderFamily.Port := by
  rw [degree_eq,Nat.card_congr (neighborsEquiv e a)]
  exact GraphFamily.graph_degree n (e a)

theorem iso_nonisolated (p : Input) (n : ℕ) (e : primal p ≃g GraphFamily.graph n) :
    Nonisolated p.1.length p.2.2 := by
  intro a
  obtain ⟨b,hb⟩ := GraphFamily.graph_neighbor n (e a)
  refine ⟨e.symm b,?_⟩
  have hh := e.symm.map_adj_iff.mpr hb
  rw [e.symm_apply_apply] at hh
  exact hh

#print axioms degree_eq
#print axioms iso_card
#print axioms iso_degree
#print axioms iso_nonisolated
end
end CSPConsequence.SparseGraphTransfer
