import Downstream.SublinearRate

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! Turn the supported-domain exponent into an input-length exponent. All
coefficients are fixed before the original domain size and tuple lists. -/
namespace CSPConsequence.SparsePowerAbsorption

noncomputable def rate (C k : ℝ) : ℝ := (2*C/Real.log 2)*k/Real.sqrt (Real.log k)

theorem rate_nonneg {C k : ℝ} (hC : 0 ≤ C) (hk : 2 ≤ k) : 0 ≤ rate C k := by
  unfold rate
  positivity

theorem domain_to_input {M : ℕ} {A C k L : ℝ} (p : ℕ)
    (hM : 2 ≤ M) (hA : 0 ≤ A) (hC : 0 ≤ C) (hk : 2 ≤ k)
    (hL : 1 ≤ L) (hML : (M:ℝ) ≤ 2*L) :
    A*L^p*Real.exp (C*LogCost.scale k (Nat.size M)) ≤
      A*2^(rate C k)*L^((p:ℝ)+rate C k) := by
  have hR := rate_nonneg hC hk
  have hLp : 0 < L := by linarith
  have hD := SublinearRate.domain_power hM hC hk
  change Real.exp (C*LogCost.scale k (Nat.size M)) ≤ (M:ℝ)^(rate C k) at hD
  calc
    _ ≤ A*L^p*(M:ℝ)^(rate C k) := mul_le_mul_of_nonneg_left hD (by positivity)
    _ ≤ A*L^p*(2*L)^(rate C k) := by
      gcongr
    _ = _ := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) hLp.le,Real.rpow_add hLp]
      simp only [Real.rpow_natCast]
      ring

theorem rate_sublinear (C : ℝ) :
    (fun k : ℝ => rate C k) =o[Filter.atTop] (fun k => k) :=
  SublinearRate.sublinear (2*C/Real.log 2)

#print axioms domain_to_input
#print axioms rate_sublinear
end CSPConsequence.SparsePowerAbsorption
