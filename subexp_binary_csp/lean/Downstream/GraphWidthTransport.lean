import Downstream.GraphWidthNumber
import Downstream.SublinearRate

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace CSPConsequence.GraphWidthTransport
noncomputable section
open OAI.BoundedTreewidthL1 GraphWidthNumber

theorem decomposition_iso {V W : Type} [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) (k : ℕ)
    (h : HasTreeDecomposition H k) : HasTreeDecomposition G k := by
  have he : GraphFamily.reindex G e.toEquiv = H := by
    ext v w
    exact e.symm.map_adj_iff
  apply GraphFamily.decomposition_of_reindex G e.toEquiv k
  rw [he]
  exact h

theorem bag_iso {V W : Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) : bagWidth G = bagWidth H := by
  apply Nat.le_antisymm
  · exact minimal G _ (decomposition_iso e _ (attained H))
  · exact minimal H _ (decomposition_iso e.symm _ (attained G))

theorem treewidth_iso {V W : Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) : treewidth G = treewidth H := by
  unfold treewidth
  rw [bag_iso e]

theorem family_comparison (n : ℕ) (hN : 64 ≤ GraphFamily.familySize n) :
    2 ≤ treewidth (GraphFamily.graph n) ∧
      (GraphFamily.familySize n:ℝ) ≤ 32*(treewidth (GraphFamily.graph n):ℝ) := by
  have hl := family_linear n
  have hNr : (64:ℝ) ≤ GraphFamily.familySize n := by exact_mod_cast hN
  have hw : (2:ℝ) ≤ treewidth (GraphFamily.graph n) := by linarith
  exact ⟨by exact_mod_cast hw,by linarith⟩

theorem exponent_transfer {A p k w : ℝ} (hA : 0 ≤ A) (hp : 0 ≤ p)
    (hw : 2 ≤ w) (hwk : w ≤ k) (hkw : k ≤ 32*w) :
    p+A*k/Real.sqrt (Real.log k) ≤ (p+32*A)*w/Real.sqrt (Real.log w) := by
  have hwpos : 0 < w := by linarith
  have hspos : 0 < Real.sqrt (Real.log w) := Real.sqrt_pos.mpr (Real.log_pos (by linarith))
  have hlogs : Real.sqrt (Real.log w) ≤ Real.sqrt (Real.log k) :=
    Real.sqrt_le_sqrt (Real.log_le_log hwpos hwk)
  have hratio : k/Real.sqrt (Real.log k) ≤ 32*w/Real.sqrt (Real.log w) := by
    calc
      _ ≤ k/Real.sqrt (Real.log w) :=
        div_le_div_of_nonneg_left (by linarith) hspos hlogs
      _ ≤ _ := div_le_div_of_nonneg_right hkw hspos.le
  have hone := LogCost.one_le_scale hw (by norm_num : (1:ℝ) ≤ 1)
  have hpbound : p ≤ p*w/Real.sqrt (Real.log w) := by
    have hh := mul_le_mul_of_nonneg_left hone hp
    unfold LogCost.scale at hh
    simpa only [one_mul,mul_one,← mul_div_assoc] using hh
  have hAbound := mul_le_mul_of_nonneg_left hratio hA
  calc
    _ = p+A*(k/Real.sqrt (Real.log k)) := by ring
    _ ≤ p*w/Real.sqrt (Real.log w)+A*(32*w/Real.sqrt (Real.log w)) := add_le_add hpbound hAbound
    _ = _ := by ring

#print axioms treewidth_iso
#print axioms family_comparison
#print axioms exponent_transfer
end
end CSPConsequence.GraphWidthTransport
