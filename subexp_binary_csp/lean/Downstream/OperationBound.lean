import Downstream.CliqueBudget
import Downstream.NativeAbsorption

set_option autoImplicit false
set_option maxHeartbeats 3000000

/-! Absorb the actual grouping operation expression, keeping its fixed-degree
input polynomial separate. No restriction is imposed on the domain bit width. -/

namespace CSPConsequence.OperationBound

open LogCost

noncomputable def coefficient {Δ : ℕ} (c : CounterExistence.Counter Δ) : ℝ :=
  54+CliqueBudget.coefficient c+72*Δ*Real.log 2+Real.log 2

theorem coefficient_nonneg {Δ : ℕ} (c : CounterExistence.Counter Δ) (hΔ : 1 ≤ Δ) :
    0 ≤ coefficient c := by
  have hc := CliqueBudget.coefficient_nonneg c hΔ
  have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  unfold coefficient
  positivity

theorem entry_exponent {K k g P Δ b : ℕ} (hK : 2 ≤ K) (hk : 2 ≤ k)
    (hu : k ≤ K^320) (hvol : g*P ≤ 2*Δ*k*b) :
    2*(g:ℝ)*P/K ≤ 72*(Δ:ℝ)*scale k b := by
  have hKr : (2:ℝ) ≤ K := by exact_mod_cast hK
  have hkr : (2:ℝ) ≤ k := by exact_mod_cast hk
  have hur : (k:ℝ) ≤ (K:ℝ)^320 := by exact_mod_cast hu
  have hi := NumericOverheads.inverse_size hKr hkr hur
  have hv : (g:ℝ)*P ≤ 2*(Δ:ℝ)*k*b := by exact_mod_cast hvol
  calc
    _ ≤ 4*(Δ:ℝ)*k*b/K := div_le_div_of_nonneg_right (by linarith) (by positivity)
    _ = (4*(Δ:ℝ)*b*k)*(1/K) := by ring
    _ ≤ (4*(Δ:ℝ)*b*k)*(18/Real.sqrt (Real.log k)) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ = _ := by unfold scale; ring

theorem grouping_bound {Δ k g P B K b E 𝒯 C₁ : ℕ}
    (c : CounterExistence.Counter Δ) (hΔ : 1 ≤ Δ) (hK : 2 ≤ K) (hk : 2 ≤ k)
    (hb : 1 ≤ b) (hl : K^32 ≤ k) (hu : k ≤ K^320) (hgK : g = 3*K^8)
    (hvol : g*P ≤ 2*Δ*k*b)
    (h𝒯 : (𝒯:ℝ) ≤ Real.exp (CliqueBudget.coefficient c*scale k b))
    (hV : g*(P+B) ≤ (2*Δ+7)*E^3) :
    ((K:ℝ)^g+𝒯*(2:ℝ)^(2*(g:ℝ)*P/K))*((g:ℝ)*(P+B))^C₁ ≤
      ((2*(Δ:ℝ)+7)^C₁)*(E:ℝ)^(3*C₁)*Real.exp (coefficient c*scale k b) := by
  have hKr : (2:ℝ) ≤ K := by exact_mod_cast hK
  have hkr : (2:ℝ) ≤ k := by exact_mod_cast hk
  have hbr : (1:ℝ) ≤ b := by exact_mod_cast hb
  have hlr : (K:ℝ)^32 ≤ k := by exact_mod_cast hl
  have hur : (k:ℝ) ≤ (K:ℝ)^320 := by exact_mod_cast hu
  have hR := one_le_scale hkr hbr
  have hgReal : (g:ℝ) = 3*(K:ℝ)^8 := by exact_mod_cast hgK
  have hsearch : (K:ℝ)^g ≤ Real.exp (54*scale k b) := by
    apply Real.le_exp_of_log_le
    rw [Real.log_pow,hgReal]
    simpa only [scale,mul_div_assoc,mul_assoc] using
      NumericOverheads.group_search hKr hkr hbr hlr hur
  have hentry : (2:ℝ)^(2*(g:ℝ)*P/K) ≤
      Real.exp ((72*(Δ:ℝ)*Real.log 2)*scale k b) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    apply Real.exp_le_exp.mpr
    have hh := entry_exponent hK hk hu hvol
    have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    nlinarith [mul_le_mul_of_nonneg_left hh hlog2]
  have hcall := NativeAbsorption.mul_exp (by positivity) h𝒯 hentry
  have hCb := CliqueBudget.coefficient_nonneg c hΔ
  have hCl : 0 ≤ 72*(Δ:ℝ)*Real.log 2 := by
    have := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)
    positivity
  have hsum := NativeAbsorption.add_exp (by norm_num : (0:ℝ)≤54)
    (add_nonneg hCb hCl) hR hsearch hcall
  have hv : (g:ℝ)*(P+B) ≤ (2*(Δ:ℝ)+7)*(E:ℝ)^3 := by exact_mod_cast hV
  have hpow : ((g:ℝ)*(P+B))^C₁ ≤ (2*(Δ:ℝ)+7)^C₁*(E:ℝ)^(3*C₁) := by
    calc
      _ ≤ ((2*(Δ:ℝ)+7)*(E:ℝ)^3)^C₁ := by gcongr
      _ = _ := by rw [mul_pow,← pow_mul]
  have hh := mul_le_mul hsum hpow (by positivity) (Real.exp_nonneg _)
  simpa only [coefficient,mul_comm,add_assoc] using hh

#print axioms entry_exponent
#print axioms grouping_bound

end CSPConsequence.OperationBound
