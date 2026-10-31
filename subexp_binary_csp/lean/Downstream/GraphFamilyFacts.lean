import Downstream.GraphTreewidth

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! The actual same-version spectral family has no isolated vertices away
from its one-vertex initial member. This supports sparse CSP normalization;
it is not a native runtime or conjecture-negation theorem. -/
namespace CSPConsequence.GraphFamily
noncomputable section
open OAI.IndependentSetsGames.Foundations.PCP
open PoweringWalks SpectralReturn
open TensorResearch.SpectralSeparation

theorem neighbor_exists {V D : Type} [Fintype V] [Fintype D]
    [Nonempty V] [Nonempty D] [DecidableEq V]
    (G : PortGraph V D) (cert : SpectralCertificate G (1/2 : Real))
    (hcard : 1 < Fintype.card V) (v : V) : ∃ w, (simple G).Adj v w := by
  classical
  by_contra h
  have hn (w : V) : ¬(simple G).Adj v w := fun hw => h ⟨w,hw⟩
  have hnext (d : D) : next G v d = v := by
    by_contra hd
    exact hn (next G v d) ⟨Ne.symm hd,d,rfl⟩
  have hsep : ∀ w d, w ∈ ({v} : Finset V) → next G w d ∉ ({v} : Finset V) →
      next G w d ∈ (∅ : Finset V) := by
    intro w d hw hout
    have he : w = v := Finset.mem_singleton.mp hw
    subst w
    exact False.elim (hout (by rw [hnext d]; exact Finset.mem_singleton_self v))
  have hs := separator_density G (1/2 : Real) cert ({v} : Finset V) ∅ hsep
  simp only [density_card,Finset.card_singleton,Finset.card_empty,Nat.cast_one,
    Nat.cast_zero,zero_div] at hs
  have hN : (1 : Real) < (Fintype.card V : Real) := by exact_mod_cast hcard
  have hNpos : (0 : Real) < (Fintype.card V : Real) := by linarith
  have ha : (0 : Real) < 1/(Fintype.card V : Real) := div_pos (by norm_num) hNpos
  have hb : (1 : Real)/(Fintype.card V : Real) < 1 :=
    (div_lt_iff₀ hNpos).2 (by simpa only [one_mul] using hN)
  have hp : (0 : Real) < (1-(1/2 : Real))*(1/(Fintype.card V : Real))*
      (1-1/(Fintype.card V : Real)) :=
    mul_pos (mul_pos (by norm_num) ha) (sub_pos.mpr hb)
  linarith

theorem family_neighbor (n : Nat)
    (v : OAI.IndependentSetsGames.Foundations.PCP.ExpanderFamily.Vertex (n+1)) :
    ∃ w, (TensorResearch.SpectralSeparation.Family.graph (n+1)).Adj v w := by
  classical
  apply neighbor_exists (OAI.IndependentSetsGames.Foundations.PCP.ExpanderFamily.family (n+1))
    (OAI.IndependentSetsGames.Foundations.PCP.ExpanderFamily.family_certificate (n+1))
  rw [OAI.IndependentSetsGames.Foundations.PCP.ExpanderFamily.card_vertex]
  exact one_lt_pow₀ OAI.IndependentSetsGames.Foundations.PCP.ExpanderFamily.growth_gt_one (by omega)

def reindex {V W : Type} (G : SimpleGraph V) (e : V ≃ W) : SimpleGraph W :=
  G.comap e.symm

def neighborEquiv {V W : Type} (G : SimpleGraph V) (e : V ≃ W) (w : W) :
    {u : W // (reindex G e).Adj w u} ≃ {v : V // G.Adj (e.symm w) v} where
  toFun u := ⟨e.symm u.val,u.property⟩
  invFun v := ⟨e v.val,by simpa only [reindex,SimpleGraph.comap_adj,Equiv.symm_apply_apply] using v.property⟩
  left_inv u := by apply Subtype.ext; exact e.apply_symm_apply _
  right_inv v := by apply Subtype.ext; exact e.symm_apply_apply _

theorem degree_reindex {V W : Type} (G : SimpleGraph V) (e : V ≃ W) (w : W) :
    Nat.card {u : W // (reindex G e).Adj w u} = Nat.card {v : V // G.Adj (e.symm w) v} :=
  Nat.card_congr (neighborEquiv G e w)

theorem mem_image_symm {V W : Type} [DecidableEq V] [DecidableEq W]
    (e : V ≃ W) (s : Finset W) (v : V) :
    v ∈ s.image e.symm ↔ e v ∈ s := by
  constructor
  · intro hv
    obtain ⟨w,hw,he⟩ := Finset.mem_image.mp hv
    have heq : w = e v := by simpa only [Equiv.apply_symm_apply] using congrArg e he
    simpa only [heq] using hw
  · intro hv
    exact Finset.mem_image.mpr ⟨e v,hv,e.symm_apply_apply v⟩

theorem decomposition_of_reindex {V W : Type} [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) (e : V ≃ W) (k : Nat)
    (h : OAI.BoundedTreewidthL1.HasTreeDecomposition (reindex G e) k) :
    OAI.BoundedTreewidthL1.HasTreeDecomposition G k := by
  obtain ⟨m,T,bag,hT,hcover,hedge,hconn,hcard⟩ := h
  refine ⟨m,T,fun t => (bag t).image e.symm,hT,?_,?_,?_,?_⟩
  · intro v
    obtain ⟨t,ht⟩ := hcover (e v)
    exact ⟨t,(mem_image_symm e (bag t) v).mpr ht⟩
  · intro u v huv
    have he : (reindex G e).Adj (e u) (e v) := by
      simpa only [reindex,SimpleGraph.comap_adj,Equiv.symm_apply_apply] using huv
    obtain ⟨t,hu,hv⟩ := hedge _ _ he
    exact ⟨t,(mem_image_symm e (bag t) u).mpr hu,(mem_image_symm e (bag t) v).mpr hv⟩
  · intro v
    have hs : {t | v ∈ (bag t).image e.symm} = {t | e v ∈ bag t} := by
      ext t
      exact mem_image_symm e (bag t) v
    exact Eq.mpr (congrArg (fun s : Set (Fin m) => (T.induce s).Connected) hs) (hconn (e v))
  · intro t
    exact Finset.card_image_le.trans (hcard t)

abbrev familySize (n : Nat) : Nat :=
  Fintype.card (OAI.IndependentSetsGames.Foundations.PCP.ExpanderFamily.Vertex (n+1))

def canonicalEquiv (n : Nat) :
    OAI.IndependentSetsGames.Foundations.PCP.ExpanderFamily.Vertex (n+1) ≃ Fin (familySize n) :=
  Fintype.equivFin _

def graph (n : Nat) : SimpleGraph (Fin (familySize n)) :=
  reindex (TensorResearch.SpectralSeparation.Family.graph (n+1)) (canonicalEquiv n)

theorem graph_degree (n : Nat) (v : Fin (familySize n)) :
    Nat.card {w // (graph n).Adj v w} ≤
      Fintype.card OAI.IndependentSetsGames.Foundations.PCP.ExpanderFamily.Port := by
  rw [graph,degree_reindex]
  exact TensorResearch.SpectralSeparation.Family.degree (n+1) _

theorem graph_neighbor (n : Nat) (v : Fin (familySize n)) :
    ∃ w, (graph n).Adj v w := by
  obtain ⟨w,hw⟩ := family_neighbor n ((canonicalEquiv n).symm v)
  refine ⟨canonicalEquiv n w,?_⟩
  simpa only [graph,reindex,SimpleGraph.comap_adj,Equiv.symm_apply_apply] using hw

theorem graph_bag_width (n k : Nat)
    (h : OAI.BoundedTreewidthL1.HasTreeDecomposition (graph n) k) :
    ((familySize n : Nat) : Real)/16 ≤ k := by
  classical
  have hd := decomposition_of_reindex (TensorResearch.SpectralSeparation.Family.graph (n+1))
    (canonicalEquiv n) k h
  have hb := TensorResearch.ExpanderTreewidth.Family.bag_width (n+1) k hd
  simpa only [familySize,OAI.IndependentSetsGames.Foundations.PCP.ExpanderFamily.card_vertex] using hb

theorem graph_unbounded : ∀ k : Nat, ∃ n : Nat,
    ¬ OAI.BoundedTreewidthL1.HasTreeDecomposition (graph n) k := by
  intro k
  refine ⟨16*k,?_⟩
  intro h
  have hb := graph_bag_width (16*k) k h
  have hp : 16*k+1 < OAI.IndependentSetsGames.Foundations.PCP.ExpanderFamily.growth^(16*k+1) :=
    (Nat.lt_two_pow_self (n := 16*k+1)).trans_le
      (Nat.pow_le_pow_left OAI.IndependentSetsGames.Foundations.PCP.ExpanderFamily.growth_gt_one _)
  have hpR : (16*k+1 : Real) < (familySize (16*k) : Real) := by
    simpa only [familySize,OAI.IndependentSetsGames.Foundations.PCP.ExpanderFamily.card_vertex,
      Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using (show
      ((16*k+1 : Nat) : Real) <
        (OAI.IndependentSetsGames.Foundations.PCP.ExpanderFamily.growth^(16*k+1) : Nat) by exact_mod_cast hp)
  linarith

#print axioms neighbor_exists
#print axioms family_neighbor
#print axioms decomposition_of_reindex
#print axioms graph_degree
#print axioms graph_neighbor
#print axioms graph_bag_width
#print axioms graph_unbounded
end
end CSPConsequence.GraphFamily
