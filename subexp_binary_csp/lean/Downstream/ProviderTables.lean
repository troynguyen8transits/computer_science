import Downstream.NodeRefinement

set_option autoImplicit false

/-! Concrete finite-input weight and interaction queries. Both scan at most
k² original vertex pairs. No assignments or crossing-label tables are listed.
Polynomial-time certificates use the existing Turing-machine implementation
library and the concrete node decoder.
-/

namespace CSPConsequence.ProviderTables

open Groundwork FiniteInput ProviderParameters NodeRefinement

def vertexList (p : Params) : List ℕ := List.range (vertices p.1)

@[fun_prop] theorem vertexList_polyT : PolyT vertexList :=
  PolyT.range (Unary.of_length (by fun_prop))

abbrev RelationQuery := Input × (ℕ × ℕ × ℕ × ℕ)

def relationBit (p : RelationQuery) : Bool :=
  if edgeAt p.1 p.2.1 p.2.2.1 then
    if p.2.1 < p.2.2.1 then
      relationAt p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2
    else relationAt p.1 p.2.2.1 p.2.1 p.2.2.2.2 p.2.2.2.1
  else true

@[fun_prop] theorem relationBit_polyT : PolyT relationBit := by
  unfold relationBit edgeAt relationAt
  fun_prop

abbrev WeightInput := Params × (ℕ × List Bool)

def weightBit (p : WeightInput) : Bool :=
  (vertexList p.1).all fun a => (vertexList p.1).all fun v =>
    if a < v ∧ a % groupCount p.1 = p.2.1 ∧ v % groupCount p.1 = p.2.1 then
      relationBit (p.1.1,a,v,nodeValue (p.1,p.2.1,p.2.2,a),nodeValue (p.1,p.2.1,p.2.2,v))
    else true

@[fun_prop] theorem weightBit_polyT : PolyT weightBit := by
  unfold weightBit groupCount
  fun_prop

def weightValue (p : WeightInput) : ℤ := if weightBit p then 1 else 0

@[fun_prop] theorem weightValue_polyT : PolyT weightValue := by
  unfold weightValue
  fun_prop

abbrev InteractionInput := Params × ((ℕ × ℕ) × (List Bool × List Bool))

def interactionBit (p : InteractionInput) : Bool :=
  (vertexList p.1).all fun a => (vertexList p.1).all fun v =>
    if a % groupCount p.1 = p.2.1.1 ∧ v % groupCount p.1 = p.2.1.2 then
      relationBit (p.1.1,a,v,nodeValue (p.1,p.2.1.1,p.2.2.1,a),
        nodeValue (p.1,p.2.1.2,p.2.2.2,v))
    else true

@[fun_prop] theorem interactionBit_polyT : PolyT interactionBit := by
  unfold interactionBit groupCount
  fun_prop

def interactionValue (p : InteractionInput) : ℤ := if interactionBit p then 1 else 0

@[fun_prop] theorem interactionValue_polyT : PolyT interactionValue := by
  unfold interactionValue
  fun_prop

#print axioms weightValue_polyT
#print axioms interactionValue_polyT

end CSPConsequence.ProviderTables
