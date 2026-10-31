import Downstream.LogCost
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false

/-! Domain-uniform conversion from the computed bit width to D, and the
little-o rate. The last two proofs port our earlier Research.CSPTransfer
lemmas to the common 4.33.1 toolchain; no compiled 4.34 interface is imported. -/

namespace CSPConsequence.SublinearRate

open Filter Asymptotics

theorem bitWidth_log {D : ℕ} (hD : 2 ≤ D) :
    (Nat.size D:ℝ) ≤ 2*Real.logb 2 (D:ℝ) := by
  have hb : 1 ≤ Nat.size D := Nat.size_pos.mpr (by omega)
  have hp : 2^(Nat.size D-1) ≤ D := by
    by_contra hh
    have hs : Nat.size D ≤ Nat.size D-1 := Nat.size_le.mpr (Nat.lt_of_not_ge hh)
    omega
  have hpr : (2:ℝ)^(Nat.size D-1) ≤ D := by exact_mod_cast hp
  have hl := Real.log_le_log (by positivity : (0:ℝ)<2^(Nat.size D-1)) hpr
  rw [Real.log_pow,Nat.cast_sub hb,Nat.cast_one] at hl
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogD : Real.log 2 ≤ Real.log (D:ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hD)
  rw [Real.logb,← mul_div_assoc]
  apply (le_div_iff₀ hlog2).mpr
  nlinarith

theorem domain_power {D : ℕ} {C k : ℝ} (hD : 2 ≤ D) (hC : 0 ≤ C) (hk : 2 ≤ k) :
    Real.exp (C*LogCost.scale k (Nat.size D)) ≤
      (D:ℝ)^((2*C/Real.log 2)*k/Real.sqrt (Real.log k)) := by
  have hb := bitWidth_log hD
  have hs : 0 ≤ Real.sqrt (Real.log k) := Real.sqrt_nonneg _
  have hd : (0:ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  calc
    _ ≤ Real.exp (C*(2*Real.logb 2 (D:ℝ))*k/Real.sqrt (Real.log k)) := by
      apply Real.exp_le_exp.mpr
      unfold LogCost.scale
      calc
        _ = (C*k/Real.sqrt (Real.log k))*(Nat.size D:ℝ) := by ring
        _ ≤ (C*k/Real.sqrt (Real.log k))*(2*Real.logb 2 (D:ℝ)) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
        _ = _ := by ring
    _ = _ := by
      rw [Real.rpow_def_of_pos hd,Real.logb]
      congr 1
      ring

theorem inverse_sqrt_log_tends_to_zero :
    Tendsto (fun x : ℝ => (Real.sqrt (Real.log x))⁻¹) atTop (nhds 0) :=
  tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop)

theorem sublinear (C : ℝ) :
    (fun x : ℝ => C*x/Real.sqrt (Real.log x)) =o[atTop] (fun x => x) := by
  apply (isLittleO_iff_tendsto (fun x hx => by simp [hx])).2
  have hlim := inverse_sqrt_log_tends_to_zero.const_mul C
  simp only [mul_zero] at hlim
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
  field_simp

#print axioms bitWidth_log
#print axioms domain_power
#print axioms sublinear

end CSPConsequence.SublinearRate
