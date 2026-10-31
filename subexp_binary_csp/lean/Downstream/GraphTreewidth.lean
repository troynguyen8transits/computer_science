import Downstream.GraphPinnedExpanderFamily
import Downstream.GraphFiniteMassSelection

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! Separator and linear bag-width arguments for the actual OAI expander family.
The three local derivation sections are consolidated to avoid repeated root
Mathlib loading. Original local draft snapshots are retained outside Research.
Pinned OAI proofs are imported from the separately attributed and checked
PinnedExpanderFamily unit. No fast CSP algorithm is assumed here; the complete
runtime/space theorem is still a separate obligation. -/


/- Local derivation section: SpectralSeparation. -/
section LocalGraphSource0

/-! Separator obstruction for the actual pinned expander family. The spectral
family is reused with attribution in PinnedExpanderFamily; the indicator and
simple-graph transfer arguments here are additional work. This is not yet a
treewidth lower bound or an algorithmic conjecture consequence. -/
namespace TensorResearch.SpectralSeparation
noncomputable section
open scoped BigOperators Classical
open OAI.IndependentSetsGames.Foundations.PCP
open PoweringWalks SpectralReturn

variable {V D : Type} [Fintype V] [Fintype D] [Nonempty V] [Nonempty D] [DecidableEq V]

def indicator (A : Finset V) (v : V) : Real := if v ∈ A then 1 else 0

def density (A : Finset V) : Real := mean (indicator A)

theorem density_card (A : Finset V) : density A = (A.card : Real)/(Fintype.card V : Real) := by
  rw [density,mean_eq_sum_div_card]
  congr 1
  simp [indicator]

theorem indicator_energy (A : Finset V) : energy (indicator A) = density A := by
  unfold energy density
  congr 1
  funext v
  by_cases h : v ∈ A <;> simp [indicator,h]

theorem correlation_bound (G : PortGraph V D) (lambda : Real)
    (cert : SpectralCertificate G lambda) (A : Finset V) :
    correlation (indicator A) (averagingOperator G (indicator A)) ≤
      (density A)^2+lambda*(density A-(density A)^2) := by
  have hm : mean (fun v => indicator A v-density A) = 0 := by
    rw [mean_sub,mean_const]
    exact sub_self _
  have he : energy (fun v => indicator A v-density A) = density A-(density A)^2 := by
    rw [energy_sub_const,indicator_energy]
    change density A-2*density A*density A+(density A)^2 = _
    ring
  have hb := zero_mean_correlation_bound G lambda cert _ hm 1
  rw [he,pow_one] at hb
  have hc := correlation_centered G (indicator A) 1
  change correlation (indicator A) (iterateOperator G 1 (indicator A)) =
    (density A)^2+correlation (fun v => indicator A v-density A)
      (iterateOperator G 1 (fun v => indicator A v-density A)) at hc
  have hh : correlation (indicator A) (iterateOperator G 1 (indicator A)) ≤
      (density A)^2+lambda*(density A-(density A)^2) := by linarith
  exact hh

theorem separator_density (G : PortGraph V D) (lambda : Real)
    (cert : SpectralCertificate G lambda) (A S : Finset V)
    (hsep : ∀ v d, v ∈ A → next G v d ∉ A → next G v d ∈ S) :
    (1-lambda)*density A*(1-density A) ≤ density S := by
  have hi (v : V) : indicator A v-indicator A v*averagingOperator G (indicator A) v ≤
      averagingOperator G (indicator S) v := by
    change indicator A v-indicator A v*mean (fun d : D => indicator A (next G v d)) ≤
      mean (fun d : D => indicator S (next G v d))
    calc
      _ = mean (fun d : D => indicator A v-indicator A v*indicator A (next G v d)) := by
        rw [mean_sub,mean_const,mean_mul_left]
      _ ≤ _ := by
        apply mean_mono
        intro d
        by_cases hv : v ∈ A
        · by_cases hw : next G v d ∈ A
          · by_cases hs : next G v d ∈ S <;> simp [indicator,hv,hw,hs]
          · have hs := hsep v d hv hw
            simp [indicator,hv,hw,hs]
        · by_cases hs : next G v d ∈ S <;> simp [indicator,hv,hs]
  have h := mean_mono hi
  rw [mean_sub,mean_operator] at h
  change density A-correlation (indicator A) (averagingOperator G (indicator A)) ≤ density S at h
  have hc := correlation_bound G lambda cert A
  nlinarith

theorem balanced_separator_density (G : PortGraph V D)
    (cert : SpectralCertificate G (1/2 : Real)) (A S : Finset V)
    (ha : 1/4 ≤ density A) (hb : density A ≤ 3/4)
    (hsep : ∀ v d, v ∈ A → next G v d ∉ A → next G v d ∈ S) :
    1/16 ≤ density S := by
  have h := separator_density G (1/2) cert A S hsep
  have hp := mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)
  nlinarith

/-- Discard loops and duplicate edges while retaining all distinct endpoints. -/
def simple (G : PortGraph V D) : SimpleGraph V where
  Adj v w := v ≠ w ∧ ∃ d, next G v d = w
  symm := ⟨by
    intro v w h
    obtain ⟨hne,d,hd⟩ := h
    refine ⟨hne.symm,(G.rot (v,d)).2,?_⟩
    have he : G.rot (v,d) = (w,(G.rot (v,d)).2) := Prod.ext hd rfl
    change (G.rot (w,(G.rot (v,d)).2)).1 = v
    rw [← he,G.rot_involutive]⟩
  loopless := ⟨fun v h => h.1 rfl⟩

def neighborPort (G : PortGraph V D) (v : V) (w : {w // (simple G).Adj v w}) : D :=
  Classical.choose w.property.2

theorem neighborPort_injective (G : PortGraph V D) (v : V) : Function.Injective (neighborPort G v) := by
  intro x y h
  apply Subtype.ext
  have hx := Classical.choose_spec x.property.2
  have hy := Classical.choose_spec y.property.2
  change next G v (neighborPort G v x) = x.val at hx
  change next G v (neighborPort G v y) = y.val at hy
  exact hx.symm.trans ((congrArg (next G v) h).trans hy)

theorem degree_bound (G : PortGraph V D) (v : V) :
    Fintype.card {w // (simple G).Adj v w} ≤ Fintype.card D :=
  Fintype.card_le_of_injective _ (neighborPort_injective G v)

theorem simple_separator_density (G : PortGraph V D)
    (cert : SpectralCertificate G (1/2 : Real)) (A S : Finset V)
    (ha : 1/4 ≤ density A) (hb : density A ≤ 3/4)
    (hsep : ∀ v ∈ A, ∀ w, w ∉ A → (simple G).Adj v w → w ∈ S) :
    1/16 ≤ density S := by
  apply balanced_separator_density G cert A S ha hb
  intro v d hv hw
  have hne : v ≠ next G v d := fun he => hw (he ▸ hv)
  exact hsep v hv _ hw ⟨hne,d,rfl⟩

namespace Family
open OAI.IndependentSetsGames.Foundations.PCP.ExpanderFamily

noncomputable def graph (n : Nat) : SimpleGraph (Vertex n) := by
  classical
  exact simple (family n)

theorem degree (n : Nat) (v : Vertex n) :
    Nat.card {w // (graph n).Adj v w} ≤ Fintype.card Port := by
  classical
  simpa only [graph,← Nat.card_eq_fintype_card] using degree_bound (family n) v

theorem separated (n : Nat) (A S : Finset (Vertex n))
    (ha : 1/4 ≤ density A) (hb : density A ≤ 3/4)
    (hsep : ∀ v ∈ A, ∀ w, w ∉ A → (graph n).Adj v w → w ∈ S) :
    1/16 ≤ density S := by
  classical
  exact simple_separator_density (family n) (family_certificate n) A S ha hb hsep

end Family
#print axioms Family.degree
#print axioms Family.separated
end
end TensorResearch.SpectralSeparation

end LocalGraphSource0


/- Local derivation section: TreeDecompositionLabels. -/
section LocalGraphSource1

/-! Actual bag decompositions induce component labels outside a selected bag.
The weighted centroid theorem is directly reused from the attributed pinned OAI
unit. This supplies the connectivity/weight interface; it does not yet prove
that a particular graph family has linear treewidth. -/
namespace TensorResearch.TreeDecompositionLabels
noncomputable section
open scoped BigOperators Classical
open SimpleGraph
open OAI.HyperbolicObstruction.PlanarRecursion

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

structure Decomposition (k : Nat) where
  size : Nat
  tree : SimpleGraph (Fin size)
  isTree : tree.IsTree
  bag : Fin size → Finset V
  cover : ∀ v, ∃ t, v ∈ bag t
  edge : ∀ v w, G.Adj v w → ∃ t, v ∈ bag t ∧ w ∈ bag t
  connected : ∀ v, (tree.induce {t | v ∈ bag t}).Connected
  bound : ∀ t, (bag t).card ≤ k

variable {G}
namespace Decomposition
variable {k : Nat} (d : Decomposition G k)

def ofHas (h : OAI.BoundedTreewidthL1.HasTreeDecomposition G k) : Decomposition G k :=
  Classical.choice (by
    obtain ⟨n,T,bag,ht,hcover,hedge,hconnected,hbound⟩ := h
    exact ⟨⟨n,T,ht,bag,hcover,hedge,hconnected,hbound⟩⟩)

def home (v : V) : Fin d.size := Classical.choose (d.cover v)

theorem home_mem (v : V) : v ∈ d.bag (d.home v) := Classical.choose_spec (d.cover v)

def weight (t : Fin d.size) : Real := ∑ v : V, if d.home v = t then 1 else 0

theorem weight_nonnegative (t : Fin d.size) : 0 ≤ d.weight t := by
  unfold weight
  apply Finset.sum_nonneg
  intro v _
  split_ifs <;> norm_num

theorem weight_total : ∑ t : Fin d.size, d.weight t = Fintype.card V := by
  unfold weight
  rw [Finset.sum_comm]
  simp

def occurrenceHom (c : Fin d.size) (v : V) (hv : v ∉ d.bag c) :
    d.tree.induce {t | v ∈ d.bag t} →g d.tree.deleteIncidenceSet c where
  toFun := Subtype.val
  map_rel' := by
    intro x y hxy
    apply deleteIncidenceSet_adj.mpr
    refine ⟨hxy,?_,?_⟩
    · intro he
      exact hv (he ▸ x.property)
    · intro he
      exact hv (he ▸ y.property)

theorem home_reachable (c : Fin d.size) (v : V) (hv : v ∉ d.bag c)
    (t : Fin d.size) (ht : v ∈ d.bag t) :
    (d.tree.deleteIncidenceSet c).Reachable (d.home v) t := by
  obtain ⟨p⟩ := (d.connected v).preconnected ⟨d.home v,d.home_mem v⟩ ⟨t,ht⟩
  exact ⟨p.map (d.occurrenceHom c v hv)⟩

theorem outside_adj (c : Fin d.size) (v w : V) (hv : v ∉ d.bag c) (hw : w ∉ d.bag c)
    (hadj : G.Adj v w) :
    (d.tree.deleteIncidenceSet c).connectedComponentMk (d.home v) =
      (d.tree.deleteIncidenceSet c).connectedComponentMk (d.home w) := by
  obtain ⟨t,hvt,hwt⟩ := d.edge v w hadj
  exact ConnectedComponent.sound
    ((d.home_reachable c v hv t hvt).trans (d.home_reachable c w hw t hwt).symm)

theorem outside_not_center (c : Fin d.size) (v : V) (hv : v ∉ d.bag c) :
    (d.tree.deleteIncidenceSet c).connectedComponentMk (d.home v) ≠
      (d.tree.deleteIncidenceSet c).connectedComponentMk c := by
  intro he
  have hh := (deleteIncidence_center_component_iff d.tree c (d.home v)).mp he
  exact hv (hh ▸ d.home_mem v)

/-- The component masses are measured using actual assigned original vertices. -/
theorem centroid_exists : ∃ c : Fin d.size,
    ∀ C : (d.tree.deleteIncidenceSet c).ConnectedComponent,
      C ≠ (d.tree.deleteIncidenceSet c).connectedComponentMk c →
      2*(∑ t ∈ C.supp.toFinset, d.weight t) ≤ Fintype.card V := by
  obtain ⟨c,hc⟩ := weighted_tree_component_separator d.tree d.isTree d.weight d.weight_nonnegative
  refine ⟨c,?_⟩
  intro C hC
  have h := hc C hC
  rw [d.weight_total] at h
  exact h

local instance component_fintype (c : Fin d.size) :
    Fintype ((d.tree.deleteIncidenceSet c).ConnectedComponent) := Fintype.ofFinite _

def vertexMass (c : Fin d.size) (C : (d.tree.deleteIncidenceSet c).ConnectedComponent) : Real :=
  ∑ v : V, if v ∉ d.bag c ∧ (d.tree.deleteIncidenceSet c).connectedComponentMk (d.home v) = C then 1 else 0

def selected (c : Fin d.size) (J : Finset ((d.tree.deleteIncidenceSet c).ConnectedComponent)) : Finset V :=
  Finset.univ.filter (fun v => v ∉ d.bag c ∧ (d.tree.deleteIncidenceSet c).connectedComponentMk (d.home v) ∈ J)

theorem selected_card (c : Fin d.size)
    (J : Finset ((d.tree.deleteIncidenceSet c).ConnectedComponent)) :
    (d.selected c J).card = ∑ C ∈ J, d.vertexMass c C := by
  symm
  unfold vertexMass
  rw [Finset.sum_comm]
  calc
    _ = ∑ v : V, if v ∉ d.bag c ∧ (d.tree.deleteIncidenceSet c).connectedComponentMk (d.home v) ∈ J
        then (1 : Real) else 0 := by
      apply Finset.sum_congr rfl
      intro v _
      by_cases hv : v ∉ d.bag c <;> simp [hv]
    _ = _ := by simp [selected]

theorem vertexMass_total (c : Fin d.size) :
    (∑ C : (d.tree.deleteIncidenceSet c).ConnectedComponent, d.vertexMass c C) =
      Fintype.card V-(d.bag c).card := by
  have hdj : Disjoint (d.selected c Finset.univ) (d.bag c) := by
    rw [Finset.disjoint_left]
    intro v hv hs
    exact (Finset.mem_filter.mp hv).2.1 hs
  have hu : d.selected c Finset.univ ∪ d.bag c = Finset.univ := by
    ext v
    by_cases hv : v ∈ d.bag c <;> simp [selected,hv]
  have hc := Finset.card_union_of_disjoint hdj
  rw [hu,Finset.card_univ] at hc
  have hreal : ((d.selected c Finset.univ).card : Real)+(d.bag c).card = Fintype.card V := by
    exact_mod_cast hc.symm
  rw [d.selected_card] at hreal
  linarith

theorem vertexMass_center (c : Fin d.size) :
    d.vertexMass c ((d.tree.deleteIncidenceSet c).connectedComponentMk c) = 0 := by
  unfold vertexMass
  apply Finset.sum_eq_zero
  intro v _
  have hn : ¬(v ∉ d.bag c ∧ (d.tree.deleteIncidenceSet c).connectedComponentMk (d.home v) =
      (d.tree.deleteIncidenceSet c).connectedComponentMk c) := by
    intro h
    exact d.outside_not_center c v h.1 h.2
  simp only [if_neg hn]

theorem vertexMass_le_weight (c : Fin d.size)
    (C : (d.tree.deleteIncidenceSet c).ConnectedComponent) :
    d.vertexMass c C ≤ ∑ t ∈ C.supp.toFinset, d.weight t := by
  unfold vertexMass weight
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro v _
  by_cases hv : v ∉ d.bag c ∧ (d.tree.deleteIncidenceSet c).connectedComponentMk (d.home v) = C
  · rw [if_pos hv]
    have hm : d.home v ∈ C.supp.toFinset := Set.mem_toFinset.mpr hv.2
    have ht := Finset.single_le_sum
      (fun t (_ : t ∈ C.supp.toFinset) => by
        split_ifs <;> norm_num : ∀ t ∈ C.supp.toFinset,
          (0 : Real) ≤ if d.home v = t then 1 else 0) hm
    simpa using ht
  · rw [if_neg hv]
    apply Finset.sum_nonneg
    intro t _
    split_ifs <;> norm_num

theorem centroid_mass : ∃ c : Fin d.size,
    ∀ C : (d.tree.deleteIncidenceSet c).ConnectedComponent,
      2*d.vertexMass c C ≤ Fintype.card V := by
  obtain ⟨c,hc⟩ := d.centroid_exists
  refine ⟨c,?_⟩
  intro C
  by_cases hC : C = (d.tree.deleteIncidenceSet c).connectedComponentMk c
  · subst C
    rw [d.vertexMass_center,mul_zero]
    positivity
  · have h := hc C hC
    have hm := d.vertexMass_le_weight c C
    linarith

end Decomposition
#print axioms Decomposition.outside_adj
#print axioms Decomposition.centroid_exists
#print axioms Decomposition.centroid_mass
#print axioms Decomposition.vertexMass_total
end
end TensorResearch.TreeDecompositionLabels

end LocalGraphSource1


/- Local derivation section: ExpanderTreewidth. -/
section LocalGraphSource2

/-! Linear bag-width obstruction for the concrete bounded-degree family.
This uses actual tree decompositions and the pinned spectral family; it assumes
no fast CSP solver. The algorithmic conjecture consequence still requires the
complete uniform bit-time and space theorem. -/
namespace TensorResearch.ExpanderTreewidth
noncomputable section
open scoped BigOperators Classical
open OAI.IndependentSetsGames.Foundations.PCP
open PoweringWalks SpectralReturn
open SpectralSeparation TreeDecompositionLabels

variable {V D : Type} [Fintype V] [Fintype D] [Nonempty V] [Nonempty D] [DecidableEq V]

theorem bag_lower_bound (H : PortGraph V D) (cert : SpectralCertificate H (1/2 : Real))
    (k : Nat) (hdecomp : OAI.BoundedTreewidthL1.HasTreeDecomposition (simple H) k) :
    (Fintype.card V : Real)/16 ≤ k := by
  by_contra h
  have hk : (k : Real) < (Fintype.card V : Real)/16 := lt_of_not_ge h
  let d : Decomposition (simple H) k := Decomposition.ofHas hdecomp
  obtain ⟨c,hc⟩ := d.centroid_mass
  letI : Fintype ((d.tree.deleteIncidenceSet c).ConnectedComponent) := Fintype.ofFinite _
  have hn : (0 : Real) < Fintype.card V := by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card V)
  have hS : ((d.bag c).card : Real) ≤ k := by exact_mod_cast d.bound c
  have hsum : (Fintype.card V : Real)/4 ≤
      ∑ C : (d.tree.deleteIncidenceSet c).ConnectedComponent, d.vertexMass c C := by
    rw [d.vertexMass_total]
    linarith
  have hbound (C : (d.tree.deleteIncidenceSet c).ConnectedComponent) :
      d.vertexMass c C ≤ (Fintype.card V : Real)/2 := by
    have hm := hc C
    linarith
  obtain ⟨J,_,hlo,hhi⟩ := FiniteMassSelection.interval Finset.univ (d.vertexMass c)
    ((Fintype.card V : Real)/4) ((Fintype.card V : Real)/2) (by positivity) hsum
    (fun C _ => hbound C)
  let A := d.selected c J
  have ha : (Fintype.card V : Real)/4 ≤ (A.card : Real) := by
    rw [show A = d.selected c J from rfl,d.selected_card]
    exact hlo
  have hb : (A.card : Real) ≤ (Fintype.card V : Real)/4+(Fintype.card V : Real)/2 := by
    rw [show A = d.selected c J from rfl,d.selected_card]
    exact hhi
  have hal : 1/4 ≤ density A := by
    rw [density_card]
    apply (le_div_iff₀ hn).2
    linarith
  have hau : density A ≤ 3/4 := by
    rw [density_card]
    apply (div_le_iff₀ hn).2
    linarith
  have hsep : ∀ v ∈ A, ∀ w, w ∉ A → (simple H).Adj v w → w ∈ d.bag c := by
    intro v hv w hw hadj
    by_contra hwS
    have hvS : v ∉ d.bag c := (Finset.mem_filter.mp hv).2.1
    have hvJ : (d.tree.deleteIncidenceSet c).connectedComponentMk (d.home v) ∈ J :=
      (Finset.mem_filter.mp hv).2.2
    have he := d.outside_adj c v w hvS hwS hadj
    have hwJ : (d.tree.deleteIncidenceSet c).connectedComponentMk (d.home w) ∈ J := he ▸ hvJ
    apply hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hwS,hwJ⟩
  have hs := simple_separator_density H cert A (d.bag c) hal hau hsep
  rw [density_card] at hs
  have hs' := (le_div_iff₀ hn).mp hs
  linarith

namespace Family
open OAI.IndependentSetsGames.Foundations.PCP.ExpanderFamily

theorem bag_width (n k : Nat)
    (h : OAI.BoundedTreewidthL1.HasTreeDecomposition (SpectralSeparation.Family.graph n) k) :
    ((growth^n : Nat) : Real)/16 ≤ k := by
  have hh := bag_lower_bound (family n) (family_certificate n) k h
  rw [card_vertex] at hh
  exact hh

private theorem growth_power (n : Nat) : n < growth^n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have hg : 2 ≤ growth := growth_gt_one
    have hm := Nat.mul_le_mul_left (growth^n) hg
    rw [pow_succ]
    nlinarith

/-- Unbounded treewidth expressed directly by the absence of uniformly bounded
bag-size decompositions, avoiding a change of treewidth conventions. -/
theorem unbounded : ∀ k : Nat, ∃ n : Nat,
    ¬ OAI.BoundedTreewidthL1.HasTreeDecomposition (SpectralSeparation.Family.graph n) k := by
  intro k
  refine ⟨16*k+1,?_⟩
  intro h
  have hb := bag_width (16*k+1) k h
  have hp := growth_power (16*k+1)
  have hpR : (16*k+1 : Real) < (growth^(16*k+1) : Nat) := by exact_mod_cast hp
  linarith

end Family
#print axioms bag_lower_bound
#print axioms Family.unbounded
end
end TensorResearch.ExpanderTreewidth

end LocalGraphSource2
