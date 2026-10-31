import Downstream.PairDecoder

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! Concrete crossing-label and factor queries on encoded finite input.
All scans are over original vertices or vertex pairs. No label assignment
space is enumerated. Semantic refinements are checked separately.
-/

namespace CSPConsequence.ProviderLabels

open Groundwork FiniteInput ProviderParameters ProviderTables PairDecoder

abbrev CrossingInput := Params × (ℕ × ℕ)

def crossingPairs (p : CrossingInput) : List (ℕ × ℕ) :=
  ((vertexList p.1).product (vertexList p.1)).filter fun q =>
    decide (q.1 % groupCount p.1 = min p.2.1 p.2.2 ∧
      q.2 % groupCount p.1 = max p.2.1 p.2.2) && edgeAt p.1.1 q.1 q.2

@[fun_prop] theorem crossingPairs_polyT : PolyT crossingPairs := by
  unfold crossingPairs groupCount edgeAt
  fun_prop

abbrev LabelReadInput := Params × ((ℕ × ℕ) × (List Bool × (ℕ × ℕ)))

def labelValue (p : LabelReadInput) : ℕ :=
  decodePairNat (domain p.1.1, blockWidth p.1, crossingPairs (p.1,p.2.1), p.2.2.1, p.2.2.2)

@[fun_prop] theorem labelValue_polyT : PolyT labelValue := by
  apply decodePairNat_polyT.comp
  unfold domain blockWidth
  fun_prop

def labelLegal (p : Params × ((ℕ × ℕ) × List Bool)) : Bool :=
  let e := crossingPairs (p.1,p.2.1)
  decide (p.2.2.length = blockWidth p.1 * e.length) &&
    e.all (fun q => decide (ofWord (readPairBlock (blockWidth p.1,e,p.2.2,q)) < domain p.1.1))

@[fun_prop] theorem labelLegal_polyT : PolyT labelLegal := by
  unfold labelLegal domain blockWidth
  dsimp only
  fun_prop

def factorBit (p : InteractionInput) : Bool :=
  if labelLegal (p.1,p.2.1,p.2.2.2) then
    (nodeMembers (p.1,p.2.1.1)).all fun a =>
      (nodeMembers (p.1,p.2.1.2)).all fun v =>
        if edgeAt p.1.1 a v then
          let z := nodeValue (p.1,p.2.1.1,p.2.2.1,a)
          let key := if p.2.1.1 < p.2.1.2 then (a,v) else (v,a)
          let y := labelValue (p.1,p.2.1,p.2.2.2,key)
          if a < v then decide (z = y) else relationAt p.1.1 v a y z
        else true
  else false

@[fun_prop] theorem factorBit_polyT : PolyT factorBit := by
  unfold factorBit edgeAt relationAt
  dsimp only
  fun_prop

def factorValue (p : InteractionInput) : ℤ := if factorBit p then 1 else 0

@[fun_prop] theorem factorValue_polyT : PolyT factorValue := by
  unfold factorValue
  fun_prop

#print axioms crossingPairs_polyT
#print axioms labelValue_polyT
#print axioms labelLegal_polyT
#print axioms factorValue_polyT

end CSPConsequence.ProviderLabels
