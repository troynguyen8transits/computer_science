import Downstream.SparseDecision
import Downstream.BitInputSizes

set_option autoImplicit false
set_option maxHeartbeats 3000000

/-! Resource-preserving connection of the sparse decision front end to the
actual total counter, and explicit constant-step runs for reduced domains 0,1. -/
namespace CSPConsequence.SparseDecisionRuns
open Groundwork Printed SparseRelabelPreparation SparseNormalization NodeRefinement
open Groundwork.Stepped

theorem check_nonisolated (p : Input) (hi : Nonisolated p.1.length p.2.2) :
    SparseIsolates.check p = true := by
  apply (SparseIsolates.check_of p).mpr
  intro a hn
  exact False.elim (hn (hi a))

theorem nonempty_nonisolated (p : Input) (hk : 0 < p.1.length)
    (hi : Nonisolated p.1.length p.2.2) : p.2.2 ≠ [] := by
  intro he
  obtain ⟨b,hb⟩ := hi ⟨0,hk⟩
  simp [he,edgeAt] at hb

theorem from_counter {Δ T S : ℕ} (c : CounterExistence.Counter Δ) (p : Input)
    (hne : p.2.2 ≠ []) (hcheck : SparseIsolates.check p = true)
    (hr : (TotalCounter.machine c).Runs (FiniteInput.tabulate (semantic p)) T S
      ((semantic p).count:ℤ)) :
    (SparseDecision.machine c).Runs p T (S+2) (SparseDecision.positive ((semantic p).count:ℤ)) := by
  rw [← prepare_eq_tabulate p] at hr
  have hh : (SparseDecision.reduced c).Runs p T S
      (SparseDecision.positive ((semantic p).count:ℤ)) := mapOut_runs (mapIn_runs hr)
  have hc := ite_runs_true (p:=SparseIsolates.check) (N:=ofFun (fun _ : Input => false)) hcheck hh
  have hm := ite_runs_false (p:=fun p : Input => p.2.2.isEmpty) (M:=ofFun SparseDecision.emptyAnswer)
    (by simp [List.isEmpty_eq_false_iff,hne]) hc
  simpa only [SparseDecision.machine,SparseDecision.checked,Nat.add_assoc] using hm

theorem small_domain {Δ k D : ℕ} (c : CounterExistence.Counter Δ) (I : Instance k D)
    (hD : D ≤ 1) :
    (TotalCounter.machine c).Runs (FiniteInput.tabulate I) 2
      (2*size (paramsOf I 1 0)+13) (I.count:ℤ) := by
  have he : TotalCounter.eligible c (FiniteInput.tabulate I) = false := by
    apply Bool.eq_false_iff.mpr
    intro ht
    have hd := ((TotalCounter.eligible_of c I).mp ht).2.1
    omega
  have hin : TotalCounter.fallbackInput (FiniteInput.tabulate I) = paramsOf I 1 0 := by
    simp [TotalCounter.fallbackInput,TotalCounter.fallbackWidth,FiniteInput.domain_tabulate,hD,paramsOf,unary]
  have hh := BruteCSP.machine_correct I 1 0 (by simpa using hD)
  have hr : TotalCounter.fallback.Runs (FiniteInput.tabulate I) 2
      (2*size (paramsOf I 1 0)+12) (I.count:ℤ) := by
    apply mapIn_runs
    rw [hin]
    simpa only [BruteCSP.bound,BruteCSP.width,ProviderParameters.blockWidth,paramsOf,unary,
      List.length_replicate,zero_mul,pow_zero,mul_one,mul_zero,add_zero] using hh
  have hm := ite_runs_false (p:=TotalCounter.eligible c) (M:=TotalCounter.fast c) he hr
  simpa only [TotalCounter.machine,Nat.add_assoc] using hm

#print axioms check_nonisolated
#print axioms from_counter
#print axioms small_domain
end CSPConsequence.SparseDecisionRuns
