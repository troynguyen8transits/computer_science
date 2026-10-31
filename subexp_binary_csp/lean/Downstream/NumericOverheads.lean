import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-! Uniform elementary overhead absorption for the selected clique size.
No runtime theorem is assumed or concluded. The bounds apply to the actual
cost expression once that expression has been established for the provider.
-/

namespace CSPConsequence.NumericOverheads

variable {K k b : ℝ}

theorem log_upper (hK : 2 ≤ K) (hk : 2 ≤ k) (hu : k ≤ K^320) :
    Real.log k ≤ 320*Real.log K := by
  have h := Real.log_le_log (by linarith : 0 < k) hu
  rw [Real.log_pow] at h
  norm_num at h
  exact h

theorem sqrt_log_upper (hK : 2 ≤ K) (hk : 2 ≤ k) (hu : k ≤ K^320) :
    Real.sqrt (Real.log k) ≤ 18*K := by
  have h1 := log_upper hK hk hu
  have h2 := Real.log_le_sub_one_of_pos (by linarith : 0 < K)
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · nlinarith

theorem group_search (hK : 2 ≤ K) (hk : 2 ≤ k) (hb : 1 ≤ b)
    (hl : K^32 ≤ k) (hu : k ≤ K^320) :
    3*K^8*Real.log K ≤ 54*b*k/Real.sqrt (Real.log k) := by
  have hs := sqrt_log_upper hK hk hu
  have hlog : Real.log K ≤ K := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hp : K^10 ≤ k := (pow_le_pow_right₀ (by linarith : 1 ≤ K) (by decide : 10 ≤ 32)).trans hl
  have hsp : 0 < Real.sqrt (Real.log k) := Real.sqrt_pos.mpr (Real.log_pos (by linarith))
  apply (le_div_iff₀ hsp).mpr
  calc
    _ ≤ 3*K^8*K*(18*K) := by gcongr
    _ = 54*K^10 := by ring
    _ ≤ 54*k := by gcongr
    _ ≤ 54*b*k := by nlinarith

theorem inverse_size (hK : 2 ≤ K) (hk : 2 ≤ k) (hu : k ≤ K^320) :
    1/K ≤ 18/Real.sqrt (Real.log k) := by
  have hs := sqrt_log_upper hK hk hu
  have hsp : 0 < Real.sqrt (Real.log k) := Real.sqrt_pos.mpr (Real.log_pos (by linarith))
  apply (div_le_div_iff₀ (by linarith : 0 < K) hsp).mpr
  simpa using hs

theorem polynomial_factor (hK : 2 ≤ K) (hk : 2 ≤ k) (hb : 1 ≤ b)
    (hl : K^32 ≤ k) (hu : k ≤ K^320) :
    K^2*(Real.log k+Real.log b+1) ≤ 5796*b*k/Real.sqrt (Real.log k) := by
  have hs := sqrt_log_upper hK hk hu
  have hlogk : Real.log k ≤ 320*K := (log_upper hK hk hu).trans
    (mul_le_mul_of_nonneg_left ((Real.log_le_sub_one_of_pos (by linarith : 0 < K)).trans (by linarith)) (by norm_num))
  have hlogb : Real.log b ≤ b := (Real.log_le_sub_one_of_pos (by linarith : 0 < b)).trans (by linarith)
  have hbK : K ≤ b*K := by nlinarith
  have hbK' : b ≤ b*K := by nlinarith
  have hbK'' : 1 ≤ b*K := by nlinarith
  have hlogs : Real.log k+Real.log b+1 ≤ 322*b*K := by nlinarith
  have hp : K^4 ≤ k := (pow_le_pow_right₀ (by linarith : 1 ≤ K) (by decide : 4 ≤ 32)).trans hl
  have hsp : 0 < Real.sqrt (Real.log k) := Real.sqrt_pos.mpr (Real.log_pos (by linarith))
  apply (le_div_iff₀ hsp).mpr
  calc
    _ ≤ K^2*(322*b*K)*(18*K) := by gcongr
    _ = 5796*b*K^4 := by ring
    _ ≤ 5796*b*k := by gcongr

#print axioms sqrt_log_upper
#print axioms group_search
#print axioms inverse_size
#print axioms polynomial_factor

end CSPConsequence.NumericOverheads
