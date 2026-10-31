import Downstream.SparseRawBits
import Downstream.BitInputSizes

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! Size bounds charged to the original sparse bit string. Complete reduced
tables are only polynomially larger; the original binary domain size does not
appear as a multiplicative cost. -/
namespace CSPConsequence.SparseSizeBounds
open Groundwork Printed SparseRelabelPreparation NodeRefinement

def ordinarySize (p : Input) : ℕ :=
  p.1.length+p.2.2.length+(SparseFields.pairs p.2.2).length+
    (SparseFields.numbers p).length+(SparseFieldBits.bitPool (SparseFields.encode p)).length+1

theorem encoding_polynomial (p : Input) :
    (SparseRawBits.encode p).length ≤ (ordinarySize p+5)^2 := by
  unfold SparseRawBits.encode
  rw [SparseFieldBits.encode_length]
  simp only [SparseFields.encode,List.length_map]
  unfold SparseFieldBits.width ordinarySize
  simp only [SparseFields.encode]
  nlinarith [Nat.zero_le (p.1.length),Nat.zero_le (p.2.2.length),
    Nat.zero_le ((SparseFields.pairs p.2.2).length),
    Nat.zero_le ((SparseFields.numbers p).length),
    Nat.zero_le ((SparseFieldBits.bitPool (SparseFields.encode p)).length)]

theorem dense_bound (p : Input) (g b K : ℕ)
    (hg : g ≤ p.1.length) (hb : b ≤ (supportList p).length) (hK : K ≤ p.1.length) :
    (BitInputCodec.encode (paramsOf (semantic p) g b,unary K)).length ≤
      17*(SparseRawBits.encode p).length^4 := by
  let L := (SparseRawBits.encode p).length
  let k := p.1.length
  let M := (supportList p).length
  have hL : 1 ≤ L := SparseRawBits.length_pos p
  have hk : k ≤ L := SparseRawBits.vertex_le_length p
  have hM : M ≤ 2*L := SparseRawBits.support_le_length p
  have hL2 : L ≤ L^2 := le_self_pow (by omega : 1 ≤ L) (by decide : 2 ≠ 0)
  have hL4 : L^2 ≤ L^4 := by
    calc
      _ ≤ (L^2)^2 := le_self_pow (one_le_pow₀ hL) (by decide : 2 ≠ 0)
      _ = _ := by ring
  have h1 : 1 ≤ L^4 := one_le_pow₀ hL
  have hk2 : k^2 ≤ L^2 := Nat.pow_le_pow_left hk 2
  have hM2 : M^2 ≤ 4*L^2 := by nlinarith [Nat.pow_le_pow_left hM 2]
  have hp : k^2*M^2 ≤ 4*L^4 := by
    calc
      _ ≤ L^2*(4*L^2) := Nat.mul_le_mul hk2 hM2
      _ = _ := by ring
  rw [BitInputCodec.encode_paramsOf_length]
  change k+M+g+b+K+5+k^2+k^2*M^2 ≤ 17*L^4
  change g ≤ k at hg
  change b ≤ M at hb
  change K ≤ k at hK
  omega

#print axioms encoding_polynomial
#print axioms dense_bound
end CSPConsequence.SparseSizeBounds
