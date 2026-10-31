import Downstream.BitInputRoundtrip

set_option autoImplicit false
set_option maxHeartbeats 3000000

/-! Binary serialization of natural-number fields. The width is bounded by
one plus the total binary length of the fields, and is explicitly charged
in the input. Every decoder is total, including on malformed strings. -/
namespace CSPConsequence.SparseFieldBits
open Groundwork Printed BitInputCodec NodeRefinement

abbrev Data := List Unit × (List Unit × (List Unit × List ℕ))
def bitPool (d : Data) : List Bool := d.2.2.2.flatMap Nat.bits
def width (d : Data) : ℕ := (bitPool d).length+1
def payload (d : Data) : List Bool := (d.2.2.2.map (toWord (width d))).flatten
def encode (d : Data) : List Bool :=
  frame d.1 (frame (unary (width d)) (frame d.2.1 (frame d.2.2.1
    (frame (unary d.2.2.2.length) (payload d)))))
def rows (w : List Bool) : List (List Bool) :=
  splitRows (header 4 w).length (header 1 w).length (rest 5 w)
def decode (w : List Bool) : Data :=
  (header 0 w,header 2 w,header 3 w,(rows w).map ofWord)

@[fun_prop] theorem bitPool_polyT : PolyT bitPool := by unfold bitPool; fun_prop
 theorem width_unary : Unary width := (Unary.of_length bitPool_polyT).add (Unary.const 1)
@[fun_prop] theorem payload_polyT : PolyT payload := by
  have ht : PolyT (fun p : Data × ℕ => toWord (width p.1) p.2) :=
    PolyT.toWord' (width_unary.comp (by fun_prop)) (by fun_prop)
  unfold payload
  fun_prop
@[fun_prop] theorem encode_polyT : PolyT encode := by
  have hw : PolyT (fun d : Data => unary (width d)) := width_unary
  have hn : PolyT (fun d : Data => unary d.2.2.2.length) := Unary.of_length (by fun_prop)
  unfold encode
  fun_prop
@[fun_prop] theorem rows_polyT : PolyT rows :=
  splitRows_polyT _ _ _ (header_unary 4) (by fun_prop) (rest_polyT 5)
@[fun_prop] theorem decode_polyT : PolyT decode := by unfold decode; fun_prop

theorem bit_length_le (xs : List ℕ) (x : ℕ) (hx : x ∈ xs) :
    (Nat.bits x).length ≤ (xs.flatMap Nat.bits).length := by
  induction xs with
  | nil => simp at hx
  | cons a xs ih =>
    simp only [List.mem_cons] at hx
    simp only [List.flatMap_cons,List.length_append]
    rcases hx with rfl | hx
    · omega
    · have h := ih hx; omega

theorem field_lt (d : Data) (x : ℕ) (hx : x ∈ d.2.2.2) : x < 2^(width d) := by
  apply Nat.size_le.mp
  rw [← Nat.size_eq_bits_len]
  have h := bit_length_le d.2.2.2 x hx
  unfold width bitPool
  omega

@[simp] theorem header_zero (d : Data) : header 0 (encode d) = d.1 := by
  simp [header,rest,encode,readUnits_frame,skip_frame]
@[simp] theorem header_one (d : Data) : header 1 (encode d) = unary (width d) := by
  simp [header,rest,encode,readUnits_frame,skip_frame]
@[simp] theorem header_two (d : Data) : header 2 (encode d) = d.2.1 := by
  simp [header,rest,encode,readUnits_frame,skip_frame]
@[simp] theorem header_three (d : Data) : header 3 (encode d) = d.2.2.1 := by
  simp [header,rest,encode,readUnits_frame,skip_frame]
@[simp] theorem header_four (d : Data) : header 4 (encode d) = unary d.2.2.2.length := by
  simp [header,rest,encode,readUnits_frame,skip_frame]
@[simp] theorem body_encode (d : Data) : rest 5 (encode d) = payload d := by
  simp [rest,encode,skip_frame]

theorem rows_encode (d : Data) : rows (encode d) = d.2.2.2.map (toWord (width d)) := by
  simp only [rows,header_four,header_one,unary,List.length_replicate,body_encode,payload]
  have hw : ∀ r ∈ d.2.2.2.map (toWord (width d)), r.length = width d := by
    intro r hr
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hr
    exact length_toWord _ _
  simpa only [List.length_map] using splitRows_flatten (d.2.2.2.map (toWord (width d))) hw

theorem decode_encode (d : Data) : decode (encode d) = d := by
  simp only [decode,header_zero,header_two,header_three,rows_encode,List.map_map]
  have h : d.2.2.2.map (ofWord ∘ toWord (width d)) = d.2.2.2 := by
    conv_rhs => rw [← List.map_id d.2.2.2]
    apply List.map_congr_left
    intro x hx
    exact ofWord_toWord (field_lt d x hx)
  rw [h]

theorem encode_length (d : Data) :
    (encode d).length = d.1.length+width d+d.2.1.length+d.2.2.1.length+
      d.2.2.2.length+5+width d*d.2.2.2.length := by
  have hl : (payload d).length = d.2.2.2.length*width d := by
    unfold payload
    rw [length_flatten_uniform, List.length_map]
    intro row hr
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hr
    exact length_toWord _ _
  simp only [encode,length_frame,unary,List.length_replicate,hl]
  ring

#print axioms encode_polyT
#print axioms decode_polyT
#print axioms decode_encode
#print axioms encode_length
end CSPConsequence.SparseFieldBits
