import Downstream.SparseSizeBounds
import Downstream.SublinearRate

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace CSPConsequence.SparseOrdinarySize
open SparseRelabelPreparation SparseSizeBounds

theorem size_pos (p : Input) : 1 ≤ ordinarySize p := by unfold ordinarySize; omega

theorem length_bound (p : Input) : (SparseRawBits.encode p).length ≤ 36*(ordinarySize p)^2 := by
  have hp := encoding_polynomial p
  have hs := size_pos p
  have hb : ordinarySize p+5 ≤ 6*ordinarySize p := by omega
  calc
    _ ≤ (ordinarySize p+5)^2 := hp
    _ ≤ (6*ordinarySize p)^2 := Nat.pow_le_pow_left hb 2
    _ = _ := by ring

theorem power_transfer (p : Input) {A r h : ℝ} (hA : 0 ≤ A) (hr : 0 ≤ r) (he : 2*r ≤ h) :
    A*((SparseRawBits.encode p).length:ℝ)^r ≤
      (A*36^r)*(ordinarySize p:ℝ)^h := by
  have hs : (1:ℝ) ≤ ordinarySize p := by exact_mod_cast size_pos p
  have hsp : (0:ℝ) < ordinarySize p := by linarith
  have hlen : ((SparseRawBits.encode p).length:ℝ) ≤ 36*(ordinarySize p:ℝ)^2 := by
    exact_mod_cast length_bound p
  calc
    _ ≤ A*(36*(ordinarySize p:ℝ)^2)^r := by gcongr
    _ = (A*36^r)*(ordinarySize p:ℝ)^(2*r) := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ)≤36) (by positivity)]
      rw [← Real.rpow_natCast (ordinarySize p:ℝ) 2,← Real.rpow_mul hsp.le]
      ring
    _ ≤ _ := by gcongr

#print axioms length_bound
#print axioms power_transfer
end CSPConsequence.SparseOrdinarySize
