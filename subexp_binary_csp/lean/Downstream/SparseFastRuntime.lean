import Downstream.SparseSizeBounds
import Downstream.SparseDecisionRuns
import Downstream.SparseNativeMachine
import Downstream.NativeFastRuntime

set_option autoImplicit false
set_option maxHeartbeats 5000000

/-! Native runtime on the original sparse string, including decoding and
support pruning. This module treats support size at least two; the 0/1 cases
use the constant-width fallback separately. -/
namespace CSPConsequence.SparseFastRuntime
open Groundwork Printed Turing SparseRelabelPreparation NodeRefinement

noncomputable def coefficient {Δ : ℕ} (c : CounterExistence.Counter Δ) (q : ℕ) : ℝ :=
  (q*(3*(CoreRuntime.timeFactor c:ℝ)+1)*((CoreRuntime.stateFactor c:ℝ)+6)^q)*
    18^(NativeFastRuntime.polynomialDegree c q)

theorem fast_for_host {Δ : ℕ} (c : CounterExistence.Counter Δ) (hΔ : 1 ≤ Δ)
    (N : TM2ComputableAux Bool Bool) (q : ℕ)
    (hhost : ∀ (p : Input) (T S : ℕ) (b : Bool), (SparseDecision.machine c).Runs p T S b →
      Nonempty (TM2OutputsInTime N.tm
        ((SparseRawBits.encode p).map N.inputAlphabet.invFun)
        (some ([b].map N.outputAlphabet.invFun))
        (q*(T+1)*((SparseRawBits.encode p).length+S+1)^q)))
    (p : Input) (hlarge : c.K 0^32 ≤ p.1.length) (hM : 2 ≤ (supportList p).length)
    (hdeg : ∀ a, (semantic p).degree a ≤ Δ)
    (hi : SparseNormalization.Nonisolated p.1.length p.2.2) :
    ∃ t, Nonempty (TM2OutputsInTime N.tm
      ((SparseRawBits.encode p).map N.inputAlphabet.invFun)
      (some ([SparseDecision.positive ((semantic p).count:ℤ)].map N.outputAlphabet.invFun)) t) ∧
      (t:ℝ) ≤ coefficient c q*
        ((SparseRawBits.encode p).length:ℝ)^(4*NativeFastRuntime.polynomialDegree c q)*
        Real.exp (NativeFastRuntime.exponentialCoefficient c q*
          LogCost.scale p.1.length (Nat.size (supportList p).length)) := by
  let k := p.1.length
  let D := (supportList p).length
  let I := semantic p
  let l := LevelSelection.select c.K k
  let K := c.K l
  let g := 3*K^8
  let b := Nat.size D
  let E := (BitInputCodec.encode (paramsOf I g b,unary K)).length
  let L := (SparseRawBits.encode p).length
  let H := E+L
  have hK : 2 ≤ K := c.levels.K_two l
  have hpos : 0 < D := by omega
  have hb : 1 ≤ b := FinitePreparation.bitWidth_pos hpos
  have hg : 0 < g := by dsimp [g]; positivity
  have hselected := LevelSelection.selected_bounds c.K k (c.levels.K_two 0)
    c.levels.K_lt c.growth10 hlarge
  have hsize : K^32 ≤ k := hselected.1
  have hu : k ≤ K^320 := hselected.2.le
  have hKk : K ≤ k := (le_self_pow (by omega : 1 ≤ K) (by decide : 32 ≠ 0)).trans hsize
  have hk : 2 ≤ k := by omega
  have hgk : g ≤ k := LevelSelection.grouping_fits hK hsize
  have hbD : b ≤ D := Nat.size_le.mpr Nat.lt_two_pow_self
  have hEL : E ≤ 17*L^4 := SparseSizeBounds.dense_bound p g b K hgk hbD hKk
  have hL1 : 1 ≤ L := SparseRawBits.length_pos p
  have hL4 : L ≤ L^4 := le_self_pow hL1 (by decide : 4 ≠ 0)
  have hHL : H ≤ 18*L^4 := by dsimp [H]; omega
  have hH1 : 1 ≤ H := by dsimp [H]; omega
  have hEH : E ≤ H := by dsimp [H]; omega
  have hLH : L ≤ H := by dsimp [H]; omega
  obtain ⟨T,S,hr,ht,hs⟩ := CoreRuntime.actual c I b l hg hpos hb
    FinitePreparation.bitWidth_capacity hΔ hdeg hsize hu rfl
  have hcounter := TotalCounter.fast_branch_runs c I hlarge hM hdeg hr
  have hne := SparseDecisionRuns.nonempty_nonisolated p (by omega) hi
  have hc := SparseDecisionRuns.check_nonisolated p hi
  have hrun := SparseDecisionRuns.from_counter c p hne hc hcounter
  have hrun' : (SparseDecision.machine c).Runs p (3*T) (S+3)
      (SparseDecision.positive ((semantic p).count:ℤ)) := by
    simpa only [Nat.add_assoc] using hrun
  let t := q*(3*T+1)*(L+(S+3)+1)^q
  refine ⟨t,hhost p (3*T) (S+3) _ hrun',?_⟩
  have hHr : (1:ℝ) ≤ H := by exact_mod_cast hH1
  have hR : 0 ≤ LogCost.scale k b :=
    (LogCost.scale_pos (by exact_mod_cast hk) (by exact_mod_cast hb)).le
  have htH : (T:ℝ) ≤ (CoreRuntime.timeFactor c:ℝ)*(H:ℝ)^(CoreRuntime.timeDegree c)*
      Real.exp (OperationBound.coefficient c*LogCost.scale k b) := by
    apply ht.trans
    gcongr <;> exact_mod_cast hEH
  have hsH : ((S+3:ℕ):ℝ) ≤ ((CoreRuntime.stateFactor c:ℝ)+3)*(H:ℝ)^(CoreRuntime.stateDegree c)+
      Real.exp (CliqueBudget.coefficient c*LogCost.scale k b) := by
    have hp : (1:ℝ) ≤ (H:ℝ)^(CoreRuntime.stateDegree c) := one_le_pow₀ hHr
    have hs' : (S:ℝ) ≤ (CoreRuntime.stateFactor c:ℝ)*(H:ℝ)^(CoreRuntime.stateDegree c)+
        Real.exp (CliqueBudget.coefficient c*LogCost.scale k b) := by
      apply hs.trans
      gcongr <;> exact_mod_cast hEH
    push_cast
    nlinarith
  have hh := NativeAbsorption.host_bound_with_input
    (CoreRuntime.stateDegree c) (CoreRuntime.timeDegree c) q
    (by unfold CoreRuntime.stateDegree; omega) hHr (by positivity) (by positivity)
    (by positivity : (0:ℝ)≤T) (by positivity : (0:ℝ)≤(S+3:ℕ))
    (OperationBound.coefficient_nonneg c hΔ) (CliqueBudget.coefficient_nonneg c hΔ) hR htH hsH
  have hAeq : ((CoreRuntime.stateFactor c:ℝ)+3)+3 = (CoreRuntime.stateFactor c:ℝ)+6 := by ring
  rw [hAeq] at hh
  let F : ℝ := q*(3*(CoreRuntime.timeFactor c:ℝ)+1)*((CoreRuntime.stateFactor c:ℝ)+6)^q
  have hF : 0 ≤ F := by dsimp [F]; positivity
  calc
    (t:ℝ) ≤ (q:ℝ)*(3*(T:ℝ)+1)*((H:ℝ)+(S+3:ℕ)+1)^q := by
      dsimp [t]
      push_cast
      gcongr <;> exact_mod_cast hLH
    _ ≤ F*(H:ℝ)^(NativeFastRuntime.polynomialDegree c q)*
        Real.exp (NativeFastRuntime.exponentialCoefficient c q*LogCost.scale k b) := hh
    _ ≤ F*(18*(L:ℝ)^4)^(NativeFastRuntime.polynomialDegree c q)*
        Real.exp (NativeFastRuntime.exponentialCoefficient c q*LogCost.scale k b) := by
      gcongr <;> exact_mod_cast hHL
    _ = _ := by
      rw [mul_pow,← pow_mul]
      unfold coefficient
      dsimp [F,L,k,D,b]
      ring

#print axioms fast_for_host
end CSPConsequence.SparseFastRuntime
