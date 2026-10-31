import Downstream.SparseFields
import Downstream.SparseFieldBits

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! Original sparse tuple-list inputs with binary domain cardinalities and
values. The counts and common bit-width headers are polynomial padding of the
usual explicit-list representation, and count as actual native input bits. -/
namespace CSPConsequence.SparseRawBits
open Groundwork SparseRelabelPreparation

def encode (p : Input) : List Bool := SparseFieldBits.encode (SparseFields.encode p)
def decode (w : List Bool) : Input := SparseFields.decode (SparseFieldBits.decode w)
@[fun_prop] theorem encode_polyT : PolyT encode :=
  SparseFieldBits.encode_polyT.comp SparseFields.encode_polyT
@[fun_prop] theorem decode_polyT : PolyT decode :=
  SparseFields.decode_polyT.comp SparseFieldBits.decode_polyT

theorem decode_encode (p : Input) : decode (encode p) = p := by
  unfold decode encode
  rw [SparseFieldBits.decode_encode,SparseFields.decode_encode]

theorem vertex_le_length (p : Input) : p.1.length ≤ (encode p).length := by
  unfold encode
  rw [SparseFieldBits.encode_length]
  simp only [SparseFields.encode]
  omega

theorem tuple_le_length (p : Input) : SparseSupport.tupleCount p.2.2 ≤ (encode p).length := by
  have h : SparseSupport.tupleCount p.2.2 = (SparseFields.pairs p.2.2).length := by
    simp [SparseSupport.tupleCount,SparseFields.pairs,List.length_flatMap]
  unfold encode
  rw [SparseFieldBits.encode_length,h]
  simp only [SparseFields.encode,List.length_map]
  omega

theorem support_le_length (p : Input) : (supportList p).length ≤ 2*(encode p).length :=
  (domain_bound p).trans (Nat.mul_le_mul_left 2 (tuple_le_length p))

theorem length_pos (p : Input) : 1 ≤ (encode p).length := by
  unfold encode
  rw [SparseFieldBits.encode_length]
  omega

#print axioms decode_polyT
#print axioms decode_encode
#print axioms vertex_le_length
#print axioms support_le_length
end CSPConsequence.SparseRawBits
