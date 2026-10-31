import Downstream.SparseSizeBounds
import Downstream.SparseDecisionRuns
import Downstream.SparseNativeMachine

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace CSPConsequence.SparseSmallRuntime
open Groundwork Printed Turing SparseRelabelPreparation NodeRefinement

 theorem small_for_host {Δ : ℕ} (c : CounterExistence.Counter Δ)
    (N : TM2ComputableAux Bool Bool) (q : ℕ)
    (hhost : ∀ (p : Input) (T S : ℕ) (b : Bool), (SparseDecision.machine c).Runs p T S b →
      Nonempty (TM2OutputsInTime N.tm
        ((SparseRawBits.encode p).map N.inputAlphabet.invFun)
        (some ([b].map N.outputAlphabet.invFun))
        (q*(T+1)*((SparseRawBits.encode p).length+S+1)^q)))
    (p : Input) (hk : 1 ≤ p.1.length) (hM : (supportList p).length ≤ 1)
    (hi : SparseNormalization.Nonisolated p.1.length p.2.2) :
    ∃ t, Nonempty (TM2OutputsInTime N.tm
      ((SparseRawBits.encode p).map N.inputAlphabet.invFun)
      (some ([SparseDecision.positive ((semantic p).count:ℤ)].map N.outputAlphabet.invFun)) t) ∧
      (t:ℝ) ≤ (3*(q:ℝ)*357^q)*((SparseRawBits.encode p).length:ℝ)^(4*q) := by
  let I := semantic p
  let L := (SparseRawBits.encode p).length
  let E := (BitInputCodec.encode (paramsOf I 1 0,unary 0)).length
  have hL1 : 1 ≤ L := SparseRawBits.length_pos p
  have hL4 : L ≤ L^4 := le_self_pow hL1 (by decide : 4 ≠ 0)
  have h14 : 1 ≤ L^4 := one_le_pow₀ hL1
  have hE : E ≤ 17*L^4 := SparseSizeBounds.dense_bound p 1 0 0 hk (by omega) (by omega)
  have hctx : size (paramsOf I 1 0) ≤ 10*E := BitInputCodec.paramsOf_size_le_encode I 1 0 0
  have hr := SparseDecisionRuns.small_domain c I hM
  have hne := SparseDecisionRuns.nonempty_nonisolated p (by omega) hi
  have hc := SparseDecisionRuns.check_nonisolated p hi
  have hsparse := SparseDecisionRuns.from_counter c p hne hc hr
  have hrun : (SparseDecision.machine c).Runs p 2 (2*size (paramsOf I 1 0)+15)
      (SparseDecision.positive ((semantic p).count:ℤ)) := by
    simpa only [Nat.add_assoc] using hsparse
  let t := q*3*(L+(2*size (paramsOf I 1 0)+15)+1)^q
  refine ⟨t,hhost p 2 _ _ hrun,?_⟩
  have hbase : L+(2*size (paramsOf I 1 0)+15)+1 ≤ 357*L^4 := by omega
  have htNat : t ≤ q*3*(357*L^4)^q :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hbase q)
  calc
    (t:ℝ) ≤ (q:ℝ)*3*(357*(L:ℝ)^4)^q := by exact_mod_cast htNat
    _ = _ := by rw [mul_pow,← pow_mul]; ring

#print axioms small_for_host
end CSPConsequence.SparseSmallRuntime
