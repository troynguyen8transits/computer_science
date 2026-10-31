import Downstream.SparseRawBits
import Downstream.SparseDecision

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! Native finite-alphabet decision machine on original sparse bit inputs.
The chosen host and simulation exponent are fixed before every sparse input. -/
namespace CSPConsequence.SparseNativeMachine
open Groundwork Turing SparseRelabelPreparation
open Groundwork.Stepped

def wordMachine {Δ : ℕ} (c : CounterExistence.Counter Δ) : Stepped (List Bool) (List Bool) :=
  mapOut (mapIn SparseRawBits.decode (SparseDecision.machine c)) (fun b => [b])

theorem wordMachine_poly {Δ : ℕ} (c : CounterExistence.Counter Δ) :
    Nonempty (IsPolyT (wordMachine c)) := by
  obtain ⟨hm⟩ := SparseDecision.machine_poly c
  letI : IsPolyT (SparseDecision.machine c) := hm
  letI : IsPolyT (mapIn SparseRawBits.decode (SparseDecision.machine c)) :=
    IsPolyT.mapIn SparseRawBits.decode_polyT
  exact ⟨IsPolyT.mapOut (by fun_prop)⟩

theorem native_from_runs {Δ : ℕ} (c : CounterExistence.Counter Δ) :
    ∃ (N : TM2ComputableAux Bool Bool) (q : ℕ), (∀ i, Finite (N.tm.Γ i)) ∧
      ∀ (p : Input) (T S : ℕ) (b : Bool), (SparseDecision.machine c).Runs p T S b →
        Nonempty (TM2OutputsInTime N.tm
          ((SparseRawBits.encode p).map N.inputAlphabet.invFun)
          (some ([b].map N.outputAlphabet.invFun))
          (q*(T+1)*((SparseRawBits.encode p).length+S+1)^q)) := by
  obtain ⟨hm⟩ := wordMachine_poly c
  letI : IsPolyT (wordMachine c) := hm
  obtain ⟨N,q,hfin,hhost⟩ := CountKSat.exists_tmW (wordMachine c)
  refine ⟨N,q,hfin,?_⟩
  intro p T S b hr
  have hi : (SparseDecision.machine c).Runs (SparseRawBits.decode (SparseRawBits.encode p)) T S b := by
    rw [SparseRawBits.decode_encode]
    exact hr
  have hw : (wordMachine c).Runs (SparseRawBits.encode p) T S [b] :=
    mapOut_runs (mapIn_runs hi)
  exact hhost _ _ _ _ hw

theorem exists_native (Δ : ℕ) (hΔ : 1 ≤ Δ) :
    ∃ (c : CounterExistence.Counter Δ) (N : TM2ComputableAux Bool Bool) (q : ℕ),
      (∀ i, Finite (N.tm.Γ i)) ∧
      (∀ (p : Input), SparseNormalization.ScopeBounded p.1.length p.2.2 →
        ∃ t b, Nonempty (TM2OutputsInTime N.tm
          ((SparseRawBits.encode p).map N.inputAlphabet.invFun)
          (some ([b].map N.outputAlphabet.invFun)) t) ∧
          (b = true ↔ SparseDecision.Satisfiable p)) ∧
      (∀ (p : Input) (T S : ℕ) (b : Bool), (SparseDecision.machine c).Runs p T S b →
        Nonempty (TM2OutputsInTime N.tm
          ((SparseRawBits.encode p).map N.inputAlphabet.invFun)
          (some ([b].map N.outputAlphabet.invFun))
          (q*(T+1)*((SparseRawBits.encode p).length+S+1)^q))) := by
  obtain ⟨c⟩ := CounterExistence.exists_counter Δ
  obtain ⟨N,q,hfin,hhost⟩ := native_from_runs c
  refine ⟨c,N,q,hfin,?_,hhost⟩
  intro p hs
  obtain ⟨T,S,b,hr,hb⟩ := SparseDecision.correct c hΔ p hs
  exact ⟨_,b,hhost p T S b hr,hb⟩

#print axioms wordMachine_poly
#print axioms native_from_runs
#print axioms exists_native
end CSPConsequence.SparseNativeMachine
