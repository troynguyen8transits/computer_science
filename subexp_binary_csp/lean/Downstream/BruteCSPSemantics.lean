import Downstream.TableRefinement
import ToTuring.Lib.Unary

set_option autoImplicit false
set_option maxHeartbeats 3000000

/-! Uniform fallback counting via all block words. The leaf uses the concrete
one-group provider's legality and relation tests, not a semantic count oracle.
There is no degree or grouping premise. Machine resource composition follows
in BruteCSPMachine. The finite-sum/network ingredients are imported directly. -/
namespace CSPConsequence.BruteCSP
open Finset Groundwork FiniteInput ProviderParameters ProviderTables NodeRefinement

def oneGroup (p : Params) : Params := (p.1,([()],p.2.2))
def width (p : Params) : Nat := blockWidth p*vertices p.1
def bound (p : Params) : Nat := 2^(width p)
def wordValue (p : Params × List Bool) : Int :=
  if nodeLegal (oneGroup p.1,0,p.2) then weightValue (oneGroup p.1,0,p.2) else 0
def leaf (p : Params × Nat) : Int := wordValue (p.1,toWord (width p.1) p.2)

theorem oneGroup_paramsOf {k D : Nat} (I : Instance k D) (g b : Nat) :
    oneGroup (paramsOf I g b) = paramsOf I 1 b := rfl
theorem width_paramsOf {k D : Nat} (I : Instance k D) (g b : Nat) :
    width (paramsOf I g b) = b*k := by simp [width,blockWidth,paramsOf,vertices_tabulate]

theorem width_unary : Unary width := by
  change Unary (fun p : Params => p.2.2.length*p.1.1.length)
  exact (Unary.of_length (by fun_prop)).mul (Unary.of_length (by fun_prop))
@[fun_prop] theorem bound_polyT : PolyT bound := by
  change PolyT (fun p : Params => 2^(width p))
  exact PolyT.two_pow width_unary
@[fun_prop] theorem wordValue_polyT : PolyT wordValue := by
  unfold wordValue oneGroup
  fun_prop
@[fun_prop] theorem leaf_polyT : PolyT leaf := by
  have hw := width_unary.comp (by fun_prop : PolyT (fun p : Params × Nat => p.1))
  have ht : PolyT (fun p : Params × Nat => toWord (width p.1) p.2) :=
    PolyT.toWord' hw (by fun_prop)
  unfold leaf
  fun_prop

theorem wordValue_natAbs (p : Params × List Bool) : (wordValue p).natAbs ≤ 1 := by
  unfold wordValue weightValue
  split_ifs <;> decide
theorem leaf_natAbs (p : Params × Nat) : (leaf p).natAbs ≤ 1 := wordValue_natAbs _
theorem leaf_size (p : Params × Nat) : size (leaf p) ≤ 2 := by
  unfold leaf wordValue weightValue
  split_ifs <;> decide

theorem members_one (k : Nat) :
    EncodedSettings.members (balanced (k := k) (g := 1) (by decide)) 0 = List.finRange k := by
  unfold EncodedSettings.members
  apply List.filter_eq_self.mpr
  intro a _
  simp only [beq_iff_eq]
  apply Fin.ext
  exact Nat.mod_one a.val

theorem network_value_one (N : Eight.SecNetworks.Net 1) :
    N.value = ∑ w ∈ N.S 0, N.W 0 w := by
  classical
  have hpairs : pairs (Fin 1) = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro p hp
    have hlt := (mem_filter.mp hp).2
    have ha := p.1.isLt
    have hb := p.2.isLt
    simp only [Fin.lt_def] at hlt
    omega
  unfold Eight.SecNetworks.Net.value
  simp only [hpairs,prod_empty,mul_one,Fin.prod_univ_one]
  apply Finset.sum_nbij (fun z : Fin 1 → List Bool => z 0)
  · intro z hz
    exact Fintype.mem_piFinset.mp hz 0
  · intro z hz z' hz' he
    funext G
    have hG : G = 0 := Subsingleton.elim _ _
    simpa only [hG] using he
  · intro w hw
    refine ⟨fun _ => w,?_,rfl⟩
    apply Fintype.mem_piFinset.mpr
    intro G
    have hG : G = 0 := Subsingleton.elim _ _
    subst G
    exact hw
  · intro z hz
    rfl

theorem sum_words_eq_count {k D : Nat} (I : Instance k D) (g b : Nat)
    (hpos : 0 < D) (hD : D ≤ 2^b) :
    (∑ w ∈ words (b*k), wordValue (paramsOf I g b,w)) = (I.count : Int) := by
  classical
  let N := BitNetwork.data I ⟨0,hpos⟩ b (balanced (g := 1) (by decide))
  have hsub : N.S 0 ⊆ words (b*k) := by
    intro w hw
    have hh := (DomainCodec.mem_encodedStates b
      (EncodedSettings.members (balanced (g := 1) (by decide)) 0) w).mp hw
    apply mem_words.mpr
    simpa only [members_one,List.length_finRange] using hh.1
  have hfilter : (words (b*k)).filter
      (fun w => nodeLegal (paramsOf I 1 b,0,w) = true) = N.S 0 := by
    ext w
    have hlegal : nodeLegal (paramsOf I 1 b,0,w) = true ↔ w ∈ N.S 0 := by
      simpa only [Fin.val_zero] using
        NodeRefinement.nodeLegal_of I b (by decide) hpos (0 : Fin 1) w
    rw [mem_filter,hlegal]
    exact and_iff_right_of_imp (fun h => hsub h)
  have hv := BitNetwork.value_eq_count I ⟨0,hpos⟩ b (balanced (g := 1) (by decide)) hD
  rw [network_value_one] at hv
  calc
    _ = ∑ w ∈ words (b*k), if nodeLegal (paramsOf I 1 b,0,w) then
        weightValue (paramsOf I 1 b,0,w) else 0 := by
      simp only [wordValue,oneGroup_paramsOf] <;> rfl
    _ = ∑ w ∈ N.S 0, weightValue (paramsOf I 1 b,0,w) := by rw [← sum_filter,hfilter]
    _ = ∑ w ∈ N.S 0, N.W 0 w := by
      apply sum_congr rfl
      intro w hw
      exact TableRefinement.weightValue_of I b (by decide) hpos (0 : Fin 1) w
    _ = _ := hv

theorem sum_leaf_eq_count {k D : Nat} (I : Instance k D) (g b : Nat)
    (hpos : 0 < D) (hD : D ≤ 2^b) :
    (∑ y ∈ range (bound (paramsOf I g b)), leaf (paramsOf I g b,y)) = (I.count : Int) := by
  simp only [bound,leaf,width_paramsOf]
  rw [sum_toWord (b*k) (fun w => wordValue (paramsOf I g b,w))]
  exact sum_words_eq_count I g b hpos hD

theorem count_empty_domain {k : Nat} (I : Instance k 0) : I.count = if k = 0 then 1 else 0 := by
  cases k with
  | zero => simp [Instance.count,Instance.valid]
  | succ k =>
    letI : IsEmpty (Fin (k+1) → Fin 0) := ⟨fun f => Fin.elim0 (f 0)⟩
    simp [Instance.count]

#print axioms leaf_polyT
#print axioms sum_leaf_eq_count
#print axioms count_empty_domain
end CSPConsequence.BruteCSP
