import Downstream.NativeFastRuntime
import Downstream.SublinearRate

set_option autoImplicit false
set_option maxHeartbeats 3000000

/-! Native domain-uniform counting theorem for canonical finite-table binary
CSP inputs. Historical sparse-format and conjecture transfer are separate;
neither is silently built into this statement. -/

namespace CSPConsequence.DenseCSPTheorem

open Groundwork Turing Filter Asymptotics

theorem exists_counter (Δ : ℕ) (hΔ : 1 ≤ Δ) :
    ∃ (N : TM2ComputableAux Bool Bool) (p k₀ : ℕ) (A C : ℝ),
      (∀ i, Finite (N.tm.Γ i)) ∧ NativeFastRuntime.Correct N ∧
      0 ≤ A ∧ 0 ≤ C ∧
      (fun x : ℝ => C*x/Real.sqrt (Real.log x)) =o[atTop] (fun x => x) ∧
      ∀ {k D : ℕ} (I : Instance k D), k₀ ≤ k → 2 ≤ D → (∀ a, I.degree a ≤ Δ) →
        ∃ t, Nonempty (TM2OutputsInTime N.tm
          ((AutomaticCounter.canonicalInput I).map N.inputAlphabet.invFun)
          (some ((Nat.bits I.count).map N.outputAlphabet.invFun)) t) ∧
          (t:ℝ) ≤ A*((AutomaticCounter.canonicalInput I).length:ℝ)^p*
            (D:ℝ)^(C*(k:ℝ)/Real.sqrt (Real.log k)) := by
  obtain ⟨c,N,q,hfin,hcorrect,hfast⟩ := NativeFastRuntime.exists_native Δ hΔ
  let A := NativeFastRuntime.polynomialCoefficient c q
  let C := 2*NativeFastRuntime.exponentialCoefficient c q/Real.log 2
  have hOp := OperationBound.coefficient_nonneg c hΔ
  have hCl := CliqueBudget.coefficient_nonneg c hΔ
  have hExp : 0 ≤ NativeFastRuntime.exponentialCoefficient c q := by
    unfold NativeFastRuntime.exponentialCoefficient
    positivity
  have hA : 0 ≤ A := by
    unfold A NativeFastRuntime.polynomialCoefficient
    positivity
  have hC : 0 ≤ C := by
    dsimp [C]
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  refine ⟨N,NativeFastRuntime.polynomialDegree c q,max 2 (c.K 0^32),A,C,
    hfin,hcorrect,hA,hC,SublinearRate.sublinear C,?_⟩
  intro k D I hlarge hD hdeg
  have hk : 2 ≤ k := (le_max_left _ _).trans hlarge
  have hlarge' : c.K 0^32 ≤ k := (le_max_right _ _).trans hlarge
  obtain ⟨t,hr,ht⟩ := hfast I hlarge' hD hdeg
  have hdomain := SublinearRate.domain_power (k := (k:ℝ)) hD hExp (by exact_mod_cast hk)
  refine ⟨t,hr,ht.trans ?_⟩
  exact mul_le_mul_of_nonneg_left hdomain (by positivity)

#print axioms exists_counter

end CSPConsequence.DenseCSPTheorem
