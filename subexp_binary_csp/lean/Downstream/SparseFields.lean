import Downstream.ListSlices
import Downstream.SparseRelabelPreparation

set_option autoImplicit false
set_option maxHeartbeats 3000000

/-! Flatten the sparse input into natural-number fields with unary counts.
This is the intermediate representation of the sparse bit codec. -/

namespace CSPConsequence.SparseFields

open Groundwork SparseNormalization SparseRelabelPreparation

abbrev Data := List Unit × (List Unit × (List Unit × List ℕ))
def pairs (cs : SparseInput) : List (ℕ × ℕ) := cs.flatMap (fun c => c.2.2)
def scopeRows (cs : SparseInput) : List (List ℕ) :=
  cs.map (fun c => [c.1,c.2.1,c.2.2.length])
def pairRows (cs : SparseInput) : List (List ℕ) :=
  (pairs cs).map (fun p => [p.1,p.2])
def numbers (p : Input) : List ℕ := p.2.1 :: ((scopeRows p.2.2).flatten++(pairRows p.2.2).flatten)
def encode (p : Input) : Data :=
  (p.1,p.2.2.map (fun _ => ()),(pairs p.2.2).map (fun _ => ()),numbers p)

@[fun_prop] theorem pairs_polyT : PolyT pairs := by unfold pairs; fun_prop
@[fun_prop] theorem scopeRows_polyT : PolyT scopeRows := by unfold scopeRows; fun_prop
@[fun_prop] theorem pairRows_polyT : PolyT pairRows := by unfold pairRows; fun_prop
@[fun_prop] theorem numbers_polyT : PolyT numbers := by unfold numbers; fun_prop
@[fun_prop] theorem encode_polyT : PolyT encode := by unfold encode; fun_prop

def scopeData (d : Data) : List (List ℕ) :=
  BitInputCodec.splitRows d.2.1.length 3 ((d.2.2.2.drop 1).take (3*d.2.1.length))
def pairData (d : Data) : List (ℕ × ℕ) :=
  (BitInputCodec.splitRows d.2.2.1.length 2 (d.2.2.2.drop (1+3*d.2.1.length))).map
    (fun r => (r.getD 0 0,r.getD 1 0))
def counts (d : Data) : List ℕ := (scopeData d).map (fun r => r.getD 2 0)
def blocks (d : Data) : List (List (ℕ × ℕ)) := ListSlices.split (counts d) (pairData d)
def constraints (d : Data) : SparseInput :=
  (List.range d.2.1.length).map (fun i =>
    let r := (scopeData d).getD i []
    (r.getD 0 0,r.getD 1 0,(blocks d).getD i []))
def decode (d : Data) : Input := (d.1,d.2.2.2.headD 0,constraints d)

@[fun_prop] theorem scopeData_polyT : PolyT scopeData := by
  unfold scopeData
  exact BitInputCodec.splitRows_polyT _ _ _ (Unary.of_length (by fun_prop)) (by fun_prop) (by fun_prop)
@[fun_prop] theorem pairData_polyT : PolyT pairData := by
  have hr : PolyT (fun d : Data => BitInputCodec.splitRows d.2.2.1.length 2
      (d.2.2.2.drop (1+3*d.2.1.length))) :=
    BitInputCodec.splitRows_polyT _ _ _ (Unary.of_length (by fun_prop)) (by fun_prop) (by fun_prop)
  unfold pairData
  exact PolyT.map (by fun_prop) hr
@[fun_prop] theorem counts_polyT : PolyT counts := by unfold counts; fun_prop
@[fun_prop] theorem blocks_polyT : PolyT blocks := ListSlices.split_polyT _ _ counts_polyT pairData_polyT
@[fun_prop] theorem constraints_polyT : PolyT constraints := by
  have hr : PolyT (fun d : Data => List.range d.2.1.length) := PolyT.range (Unary.of_length (by fun_prop))
  unfold constraints
  fun_prop
@[fun_prop] theorem decode_polyT : PolyT decode := by unfold decode; fun_prop

theorem scope_flat_length (cs : SparseInput) : (scopeRows cs).flatten.length = 3*cs.length := by
  simp [scopeRows,List.length_flatten,List.map_map,Function.comp_def,List.map_const,List.sum_replicate,mul_comm]
theorem pair_flat_length (cs : SparseInput) : (pairRows cs).flatten.length = 2*(pairs cs).length := by
  simp [pairRows,List.length_flatten,List.map_map,Function.comp_def,List.map_const,List.sum_replicate,mul_comm]
theorem numbers_length (p : Input) : (numbers p).length = 1+3*p.2.2.length+2*(pairs p.2.2).length := by
  simp only [numbers,List.length_cons,List.length_append,scope_flat_length,pair_flat_length]
  omega

theorem scopeData_encode (p : Input) : scopeData (encode p) = scopeRows p.2.2 := by
  have hp : ((numbers p).drop 1).take (3*p.2.2.length) = (scopeRows p.2.2).flatten := by
    simp only [numbers,List.drop_succ_cons,List.drop_zero]
    rw [← scope_flat_length]
    exact List.take_left
  simp only [scopeData,encode,List.length_map]
  rw [hp]
  have hw : ∀ r ∈ scopeRows p.2.2, r.length = 3 := by
    intro r hr
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hr
    rfl
  simpa only [scopeRows,List.length_map] using BitInputCodec.splitRows_flatten (scopeRows p.2.2) hw

theorem pairData_encode (p : Input) : pairData (encode p) = pairs p.2.2 := by
  have hp : (numbers p).drop (1+3*p.2.2.length) = (pairRows p.2.2).flatten := by
    rw [Nat.add_comm 1]
    simp only [numbers,List.drop_succ_cons]
    rw [← scope_flat_length,List.drop_left]
  simp only [pairData,encode,List.length_map]
  rw [hp]
  have hw : ∀ r ∈ pairRows p.2.2, r.length = 2 := by
    intro r hr
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hr
    rfl
  have hh := BitInputCodec.splitRows_flatten (pairRows p.2.2) hw
  rw [show (pairRows p.2.2).length = (pairs p.2.2).length from by simp [pairRows]] at hh
  rw [hh]
  simp [pairRows,List.map_map,Function.comp_def]

theorem counts_encode (p : Input) : counts (encode p) = p.2.2.map (fun c => c.2.2.length) := by
  rw [counts,scopeData_encode]
  simp [scopeRows,List.map_map,Function.comp_def]

theorem blocks_encode (p : Input) : blocks (encode p) = p.2.2.map (fun c => c.2.2) := by
  rw [blocks,counts_encode,pairData_encode]
  simpa only [List.map_map,Function.comp_def,List.flatMap_def,pairs] using
    ListSlices.split_flatten (p.2.2.map (fun c => c.2.2))

theorem constraints_encode (p : Input) : constraints (encode p) = p.2.2 := by
  simp only [constraints,encode,List.length_map]
  change (List.range p.2.2.length).map (fun i =>
    let r := (scopeData (encode p)).getD i []
    (r.getD 0 0,r.getD 1 0,(blocks (encode p)).getD i [])) = p.2.2
  rw [scopeData_encode,blocks_encode]
  apply List.ext_getElem (by simp)
  intro i hi hj
  have hik : i < p.2.2.length := by simpa using hi
  simp [scopeRows,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hik]

theorem decode_encode (p : Input) : decode (encode p) = p := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · exact constraints_encode p

#print axioms encode_polyT
#print axioms decode_polyT
#print axioms numbers_length
#print axioms decode_encode

end CSPConsequence.SparseFields
