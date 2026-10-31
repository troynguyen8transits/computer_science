import Downstream.GraphFamilyFacts

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! Numerical treewidth from the actual bag-decomposition definition. The
minimum bag cardinality is treewidth plus one on the nonempty family. -/
namespace CSPConsequence.GraphWidthNumber
noncomputable section
open scoped Classical
open OAI.BoundedTreewidthL1

 theorem one_bag {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    HasTreeDecomposition G (Fintype.card V) := by
  classical
  refine ⟨1,⊥,fun _ => Finset.univ,SimpleGraph.IsTree.of_subsingleton,?_,?_,?_,?_⟩
  · intro v; exact ⟨0,Finset.mem_univ _⟩
  · intro u v h; exact ⟨0,Finset.mem_univ _,Finset.mem_univ _⟩
  · intro v
    refine { preconnected := SimpleGraph.Preconnected.of_subsingleton,
             nonempty := ⟨⟨0,Finset.mem_univ _⟩⟩ }
  · intro t; simp

def bagWidth {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : ℕ :=
  Nat.find (show ∃ k, HasTreeDecomposition G k from ⟨_,one_bag G⟩)
def treewidth {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : ℕ := bagWidth G-1

theorem attained {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    HasTreeDecomposition G (bagWidth G) := Nat.find_spec _
theorem minimal {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (k : ℕ) (h : HasTreeDecomposition G k) : bagWidth G ≤ k := Nat.find_min' _ h
theorem bag_le_card {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    bagWidth G ≤ Fintype.card V := minimal G _ (one_bag G)
theorem bag_pos {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) :
    1 ≤ bagWidth G := by
  classical
  obtain ⟨n,T,bag,ht,hcover,he,hc,hbound⟩ := attained G
  obtain ⟨v⟩ := (inferInstance : Nonempty V)
  obtain ⟨t,hv⟩ := hcover v
  have hp : 0 < (bag t).card := Finset.card_pos.mpr ⟨v,hv⟩
  have hb := hbound t
  omega

theorem bag_eq_tw_add_one {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) : bagWidth G = treewidth G+1 := by
  have h := bag_pos G
  unfold treewidth
  omega

open GraphFamily OAI.IndependentSetsGames.Foundations.PCP.ExpanderFamily

theorem family_size_pos (n : ℕ) : 0 < familySize n := by
  rw [familySize,card_vertex]
  exact pow_pos (by have h := growth_gt_one; omega) _
theorem family_bag_eq (n : ℕ) : bagWidth (graph n) = treewidth (graph n)+1 := by
  letI : Nonempty (Fin (familySize n)) := ⟨⟨0,family_size_pos n⟩⟩
  exact bag_eq_tw_add_one _
theorem family_linear (n : ℕ) : (familySize n:ℝ)/16 ≤ (treewidth (graph n):ℝ)+1 := by
  have h := graph_bag_width n (bagWidth (graph n)) (attained _)
  rw [family_bag_eq] at h
  exact_mod_cast h
theorem family_tw_le (n : ℕ) : treewidth (graph n) ≤ familySize n := by
  have h := bag_le_card (graph n)
  simp only [Fintype.card_fin] at h
  unfold treewidth
  omega

theorem family_size_grows (n : ℕ) : n+1 < familySize n := by
  rw [familySize,card_vertex]
  exact (Nat.lt_two_pow_self (n:=n+1)).trans_le (Nat.pow_le_pow_left growth_gt_one _)

theorem tail_unbounded (cutoff w : ℕ) :
    ∃ n, cutoff ≤ familySize n ∧ w < treewidth (graph n) := by
  let n := cutoff+16*(w+2)
  have hn := family_size_grows n
  have hl := family_linear n
  have hN : (16*(w+2):ℝ) < (familySize n:ℝ) := by
    exact_mod_cast (show 16*(w+2) < familySize n by omega)
  refine ⟨n,by omega,?_⟩
  have htw : (w:ℝ) < (treewidth (graph n):ℝ) := by linarith
  exact_mod_cast htw

#print axioms one_bag
#print axioms bag_eq_tw_add_one
#print axioms family_linear
#print axioms tail_unbounded
end
end CSPConsequence.GraphWidthNumber
