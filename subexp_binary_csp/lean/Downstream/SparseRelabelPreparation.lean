import Downstream.SparseSupportDomain
import Printed.GroupingProcs

set_option autoImplicit false
set_option maxHeartbeats 3000000

/-! Polynomial-time complete-table preparation after global support pruning.
The original domain cardinality is a binary natural number, not a unary list.
The output domain has at most twice the number of listed tuples. -/

namespace CSPConsequence.SparseRelabelPreparation

open Groundwork SparseNormalization

abbrev Input := List Unit × (ℕ × SparseInput)
def supportList (p : Input) : List ℕ := SparseSupport.support p.2.1 p.2.2
def value (p : Input × ℕ) : ℕ := (supportList p.1).getD p.2 0
def vertexList (p : Input) : List ℕ := List.range p.1.length
def domainList (p : Input) : List ℕ := List.range (supportList p).length

@[fun_prop] theorem supportList_polyT : PolyT supportList :=
  SparseSupport.support_polyT.comp (by fun_prop)
@[fun_prop] theorem value_polyT : PolyT value := by unfold value; fun_prop
@[fun_prop] theorem vertexList_polyT : PolyT vertexList :=
  PolyT.range (Unary.of_length (by fun_prop))
@[fun_prop] theorem domainList_polyT : PolyT domainList :=
  PolyT.range (Unary.of_length supportList_polyT)

def prepare (p : Input) : FiniteInput.Input :=
  (p.1,(supportList p).map (fun _ => ()),
    (vertexList p).map (fun a => (vertexList p).map (fun b => edgeAt p.2.2 a b)),
    (vertexList p).map (fun a => (vertexList p).map (fun b =>
      (domainList p).map (fun x => (domainList p).map (fun y =>
        relationAt p.2.2 a b (value (p,x)) (value (p,y)))))))

@[fun_prop] theorem prepare_polyT : PolyT prepare := by
  unfold prepare
  fun_prop

def semantic (p : Input) : Instance p.1.length (supportList p).length :=
  SparseSupportDomain.restricted p.2.2 (normalized p.1.length p.2.1 p.2.2)

theorem value_of (p : Input) (x : Fin (supportList p).length) :
    value (p,x.val) = (SparseSupportDomain.decode p.2.1 p.2.2 x).val := by
  change (supportList p).getD x.val 0 = (supportList p).get x
  simp [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem x.isLt]

theorem unit_list (u : List Unit) : u = List.replicate u.length () :=
  List.eq_replicate_iff.mpr ⟨rfl,fun a _ => Subsingleton.elim _ _⟩

theorem prepare_eq_tabulate (p : Input) : prepare p = FiniteInput.tabulate (semantic p) := by
  unfold prepare FiniteInput.tabulate
  apply Prod.ext
  · exact unit_list p.1
  · apply Prod.ext
    · exact List.map_const'
    · apply Prod.ext
      · unfold vertexList
        apply Printed.map_range_eq_ofFn
        intro a
        apply Printed.map_range_eq_ofFn
        intro b
        rfl
      · unfold vertexList domainList
        apply Printed.map_range_eq_ofFn
        intro a
        apply Printed.map_range_eq_ofFn
        intro b
        apply Printed.map_range_eq_ofFn
        intro x
        apply Printed.map_range_eq_ofFn
        intro y
        change relationAt p.2.2 a.val b.val (value (p,x.val)) (value (p,y.val)) =
          relationAt p.2.2 a.val b.val
            (SparseSupportDomain.decode p.2.1 p.2.2 x).val
            (SparseSupportDomain.decode p.2.1 p.2.2 y).val
        rw [value_of p x,value_of p y]

theorem domain_bound (p : Input) : (supportList p).length ≤ 2*SparseSupport.tupleCount p.2.2 :=
  SparseSupport.support_bound p.2.1 p.2.2

theorem count_eq (p : Input) (hs : ScopeBounded p.1.length p.2.2)
    (hni : Nonisolated p.1.length p.2.2) :
    (semantic p).count = rawCount (k:=p.1.length) (D:=p.2.1) p.2.2 :=
  SparseSupportDomain.normalized_count p.2.2 hs hni

#print axioms prepare_polyT
#print axioms prepare_eq_tabulate
#print axioms domain_bound
#print axioms count_eq

end CSPConsequence.SparseRelabelPreparation
