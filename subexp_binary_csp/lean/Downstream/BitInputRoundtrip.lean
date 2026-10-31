import Downstream.BitInputCodec

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace CSPConsequence.BitInputCodec
open Groundwork Printed FiniteInput ProviderParameters DynamicPreparation NodeRefinement

structure Rectangular (p : PreparedInput) : Prop where
  edgeCount : p.1.1.2.2.1.length = p.1.1.1.length
  edgeWidth : ∀ row ∈ p.1.1.2.2.1, row.length = p.1.1.1.length
  relationCount : p.1.1.2.2.2.length = p.1.1.1.length
  relationWidth : ∀ rows ∈ p.1.1.2.2.2, rows.length = p.1.1.1.length
  pairWidth : ∀ rows ∈ p.1.1.2.2.2.flatten, rows.length = p.1.1.2.1.length
  rowWidth : ∀ row ∈ p.1.1.2.2.2.flatten.flatten, row.length = p.1.1.2.1.length

theorem length_flatten_uniform {α : Type} {width : Nat} (L : List (List α))
    (h : ∀ row ∈ L, row.length = width) : L.flatten.length = L.length*width := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have ha := h a (by simp)
    have ht := ih (fun row hr => h row (by simp [hr]))
    simp only [List.flatten_cons,List.length_append,List.length_cons,ha,ht,Nat.succ_mul]
    omega

theorem rectangular_paramsOf {k D : Nat} (I : Instance k D) (g b K : Nat) :
    Rectangular (paramsOf I g b,unary K) := by
  constructor
  · simp [paramsOf,tabulate]
  · intro row h
    rcases List.mem_ofFn.mp h with ⟨a,rfl⟩
    simp [paramsOf,tabulate]
  · simp [paramsOf,tabulate]
  · intro rows h
    rcases List.mem_ofFn.mp h with ⟨a,rfl⟩
    simp [paramsOf,tabulate]
  · intro rows h
    rcases List.mem_flatten.mp h with ⟨outer,ho,hr⟩
    rcases List.mem_ofFn.mp ho with ⟨a,rfl⟩
    rcases List.mem_ofFn.mp hr with ⟨v,rfl⟩
    simp [paramsOf,tabulate]
  · intro row h
    rcases List.mem_flatten.mp h with ⟨middle,hm,hr⟩
    rcases List.mem_flatten.mp hm with ⟨outer,ho,hmid⟩
    rcases List.mem_ofFn.mp ho with ⟨a,rfl⟩
    rcases List.mem_ofFn.mp hmid with ⟨v,rfl⟩
    rcases List.mem_ofFn.mp hr with ⟨x,rfl⟩
    simp [paramsOf,tabulate]

@[simp] theorem header_encode_zero (p : PreparedInput) : header 0 (encode p) = p.1.1.1 := by
  simp [header,rest,encode,readUnits_frame,skip_frame]
@[simp] theorem header_encode_one (p : PreparedInput) : header 1 (encode p) = p.1.1.2.1 := by
  simp [header,rest,encode,readUnits_frame,skip_frame]
@[simp] theorem header_encode_two (p : PreparedInput) : header 2 (encode p) = p.1.2.1 := by
  simp [header,rest,encode,readUnits_frame,skip_frame]
@[simp] theorem header_encode_three (p : PreparedInput) : header 3 (encode p) = p.1.2.2 := by
  simp [header,rest,encode,readUnits_frame,skip_frame]
@[simp] theorem header_encode_four (p : PreparedInput) : header 4 (encode p) = p.2 := by
  simp [header,rest,encode,readUnits_frame,skip_frame]
@[simp] theorem body_encode (p : PreparedInput) :
    rest 5 (encode p) = p.1.1.2.2.1.flatten ++ p.1.1.2.2.2.flatten.flatten.flatten := by
  simp [rest,encode,skip_frame]

theorem edge_length (p : PreparedInput) (h : Rectangular p) :
    p.1.1.2.2.1.flatten.length = p.1.1.1.length^2 := by
  rw [length_flatten_uniform _ h.edgeWidth,h.edgeCount,pow_two]

theorem relation_pair_length (p : PreparedInput) (h : Rectangular p) :
    p.1.1.2.2.2.flatten.length = p.1.1.1.length^2 := by
  rw [length_flatten_uniform _ h.relationWidth,h.relationCount,pow_two]

theorem relation_leaf_length (p : PreparedInput) (h : Rectangular p) :
    p.1.1.2.2.2.flatten.flatten.length = p.1.1.1.length^2*p.1.1.2.1.length := by
  rw [length_flatten_uniform _ h.pairWidth,relation_pair_length p h]

theorem relation_length (p : PreparedInput) (h : Rectangular p) :
    p.1.1.2.2.2.flatten.flatten.flatten.length = p.1.1.1.length^2*p.1.1.2.1.length^2 := by
  rw [length_flatten_uniform _ h.rowWidth,relation_leaf_length p h]
  ring

theorem edgeBits_encode (p : PreparedInput) (h : Rectangular p) :
    edgeBits (encode p) = p.1.1.2.2.1.flatten := by
  simp only [edgeBits,body_encode,header_encode_zero]
  rw [← edge_length p h,List.take_left]

theorem relationBits_encode (p : PreparedInput) (h : Rectangular p) :
    relationBits (encode p) = p.1.1.2.2.2.flatten.flatten.flatten := by
  simp only [relationBits,body_encode,header_encode_zero]
  rw [← edge_length p h,List.drop_left]

theorem edgeRows_encode (p : PreparedInput) (h : Rectangular p) :
    edgeRows (encode p) = p.1.1.2.2.1 := by
  simp only [edgeRows,header_encode_zero,edgeBits_encode p h]
  simpa only [h.edgeCount] using splitRows_flatten p.1.1.2.2.1 h.edgeWidth

theorem leafRows_encode (p : PreparedInput) (h : Rectangular p) :
    leafRows (encode p) = p.1.1.2.2.2.flatten.flatten := by
  simp only [leafRows,header_encode_zero,header_encode_one,relationBits_encode p h]
  simpa only [relation_leaf_length p h] using
    splitRows_flatten p.1.1.2.2.2.flatten.flatten h.rowWidth

theorem pairRows_encode (p : PreparedInput) (h : Rectangular p) :
    pairRows (encode p) = p.1.1.2.2.2.flatten := by
  simp only [pairRows,header_encode_zero,header_encode_one,leafRows_encode p h]
  simpa only [relation_pair_length p h] using splitRows_flatten p.1.1.2.2.2.flatten h.pairWidth

theorem relationRows_encode (p : PreparedInput) (h : Rectangular p) :
    relationRows (encode p) = p.1.1.2.2.2 := by
  simp only [relationRows,header_encode_zero,pairRows_encode p h]
  simpa only [h.relationCount] using splitRows_flatten p.1.1.2.2.2 h.relationWidth

theorem decode_encode (p : PreparedInput) (h : Rectangular p) : decode (encode p) = p := by
  simp only [decode,header_encode_zero,header_encode_one,header_encode_two,header_encode_three,
    header_encode_four,edgeRows_encode p h,relationRows_encode p h]

theorem decode_encode_paramsOf {k D : Nat} (I : Instance k D) (g b K : Nat) :
    decode (encode (paramsOf I g b,unary K)) = (paramsOf I g b,unary K) :=
  decode_encode _ (rectangular_paramsOf I g b K)

theorem length_frame (u : List Unit) (w : List Bool) : (frame u w).length = u.length+1+w.length := by
  simp [frame]
  omega

theorem encode_length (p : PreparedInput) (h : Rectangular p) :
    (encode p).length = p.1.1.1.length+p.1.1.2.1.length+p.1.2.1.length+p.1.2.2.length+p.2.length+5+
      p.1.1.1.length^2+p.1.1.1.length^2*p.1.1.2.1.length^2 := by
  simp only [encode,length_frame,List.length_append,edge_length p h,relation_length p h]
  omega

theorem encode_paramsOf_length {k D : Nat} (I : Instance k D) (g b K : Nat) :
    (encode (paramsOf I g b,unary K)).length = k+D+g+b+K+5+k^2+k^2*D^2 := by
  simpa only [paramsOf,tabulate,unary,List.length_replicate] using
    encode_length _ (rectangular_paramsOf I g b K)

#print axioms decode_encode_paramsOf
#print axioms encode_paramsOf_length
end CSPConsequence.BitInputCodec
