import Downstream.SparseFastRuntime
import Downstream.SparseSmallRuntime
import Downstream.SparsePowerAbsorption

set_option autoImplicit false
set_option maxHeartbeats 5000000

namespace CSPConsequence.SparseUniformRuntime
open Groundwork Turing SparseRelabelPreparation

 def degree {Δ : ℕ} (c : CounterExistence.Counter Δ) (q : ℕ) : ℕ :=
  4*NativeFastRuntime.polynomialDegree c q+4*q
 noncomputable def factor {Δ : ℕ} (c : CounterExistence.Counter Δ) (q : ℕ) : ℝ :=
  SparseFastRuntime.coefficient c q+3*(q:ℝ)*357^q+1
 noncomputable def rate {Δ : ℕ} (c : CounterExistence.Counter Δ) (q : ℕ) (k : ℝ) : ℝ :=
  SparsePowerAbsorption.rate (NativeFastRuntime.exponentialCoefficient c q) k
 noncomputable def prefactor {Δ : ℕ} (c : CounterExistence.Counter Δ) (q : ℕ) (k : ℝ) : ℝ :=
  factor c q*2^(rate c q k)

 theorem exponential_nonneg {Δ : ℕ} (c : CounterExistence.Counter Δ) (hΔ : 1 ≤ Δ) (q : ℕ) :
    0 ≤ NativeFastRuntime.exponentialCoefficient c q := by
  unfold NativeFastRuntime.exponentialCoefficient
  exact add_nonneg (OperationBound.coefficient_nonneg c hΔ)
    (mul_nonneg (by positivity) (CliqueBudget.coefficient_nonneg c hΔ))
 theorem factor_nonneg {Δ : ℕ} (c : CounterExistence.Counter Δ) (q : ℕ) : 0 ≤ factor c q := by
  unfold factor SparseFastRuntime.coefficient
  positivity

 theorem fast_for_host {Δ : ℕ} (c : CounterExistence.Counter Δ) (hΔ : 1 ≤ Δ)
    (N : TM2ComputableAux Bool Bool) (q : ℕ)
    (hhost : ∀ (p : Input) (T S : ℕ) (b : Bool), (SparseDecision.machine c).Runs p T S b →
      Nonempty (TM2OutputsInTime N.tm
        ((SparseRawBits.encode p).map N.inputAlphabet.invFun)
        (some ([b].map N.outputAlphabet.invFun))
        (q*(T+1)*((SparseRawBits.encode p).length+S+1)^q)))
    (p : Input) (hlarge : c.K 0^32 ≤ p.1.length)
    (hdeg : ∀ a, (semantic p).degree a ≤ Δ)
    (hi : SparseNormalization.Nonisolated p.1.length p.2.2) :
    ∃ t, Nonempty (TM2OutputsInTime N.tm
      ((SparseRawBits.encode p).map N.inputAlphabet.invFun)
      (some ([SparseDecision.positive ((semantic p).count:ℤ)].map N.outputAlphabet.invFun)) t) ∧
      (t:ℝ) ≤ prefactor c q p.1.length*
        ((SparseRawBits.encode p).length:ℝ)^((degree c q:ℝ)+rate c q p.1.length) := by
  let L : ℝ := (SparseRawBits.encode p).length
  let k : ℝ := p.1.length
  let C := NativeFastRuntime.exponentialCoefficient c q
  have hC : 0 ≤ C := exponential_nonneg c hΔ q
  have hK : 2 ≤ c.K 0 := c.levels.K_two 0
  have hKpow : c.K 0 ≤ c.K 0^32 := le_self_pow (by omega : 1 ≤ c.K 0) (by decide : 32 ≠ 0)
  have hknat : 2 ≤ p.1.length := by omega
  have hk : 2 ≤ k := by dsimp [k]; exact_mod_cast hknat
  have hL : 1 ≤ L := by dsimp [L]; exact_mod_cast SparseRawBits.length_pos p
  have hLpos : 0 < L := by linarith
  have hR : 0 ≤ rate c q k := SparsePowerAbsorption.rate_nonneg hC hk
  have hA : 0 ≤ SparseFastRuntime.coefficient c q := by unfold SparseFastRuntime.coefficient; positivity
  have hF := factor_nonneg c q
  by_cases hM : 2 ≤ (supportList p).length
  · obtain ⟨t,hnative,ht⟩ := SparseFastRuntime.fast_for_host c hΔ N q hhost p hlarge hM hdeg hi
    refine ⟨t,hnative,?_⟩
    have hp : 4*NativeFastRuntime.polynomialDegree c q ≤ degree c q := by unfold degree; omega
    have ht' : (t:ℝ) ≤ SparseFastRuntime.coefficient c q*L^(degree c q)*
        Real.exp (C*LogCost.scale k (Nat.size (supportList p).length)) := by
      apply ht.trans
      gcongr
    have hML : ((supportList p).length:ℝ) ≤ 2*L := by dsimp [L]; exact_mod_cast SparseRawBits.support_le_length p
    have hab := SparsePowerAbsorption.domain_to_input (degree c q) hM hA hC hk hL hML
    have hAF : SparseFastRuntime.coefficient c q ≤ factor c q := by
      have hsmall : (0:ℝ) ≤ 3*(q:ℝ)*357^q := by positivity
      unfold factor
      linarith
    calc
      _ ≤ SparseFastRuntime.coefficient c q*2^(rate c q k)*L^((degree c q:ℝ)+rate c q k) := ht'.trans hab
      _ ≤ _ := by unfold prefactor; gcongr
  · have hsmall : (supportList p).length ≤ 1 := by omega
    obtain ⟨t,hnative,ht⟩ := SparseSmallRuntime.small_for_host c N q hhost p
      (by omega) hsmall hi
    refine ⟨t,hnative,?_⟩
    have hp : 4*q ≤ degree c q := by unfold degree; omega
    have ht' : (t:ℝ) ≤ (3*(q:ℝ)*357^q)*L^(degree c q) := by
      apply ht.trans
      gcongr
    have hAF : 3*(q:ℝ)*357^q ≤ factor c q := by unfold factor; linarith
    have h2 : 1 ≤ (2:ℝ)^(rate c q k) := Real.one_le_rpow (by norm_num) hR
    have hLR : 1 ≤ L^(rate c q k) := Real.one_le_rpow hL hR
    calc
      _ ≤ factor c q*L^(degree c q) := ht'.trans (mul_le_mul_of_nonneg_right hAF (by positivity))
      _ ≤ (factor c q*L^(degree c q))*(2^(rate c q k)*L^(rate c q k)) :=
        le_mul_of_one_le_right (by positivity) (one_le_mul_of_one_le_of_one_le h2 hLR)
      _ = _ := by
        unfold prefactor
        rw [Real.rpow_add hLpos]
        simp only [Real.rpow_natCast]
        ring

#print axioms exponential_nonneg
#print axioms fast_for_host
end CSPConsequence.SparseUniformRuntime
