import Downstream.CostParameters
import Downstream.QuerySizes

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! The non-clique state terms are polynomial in actual bit-input length.
Their degrees depend only on the fixed counter constants, not k or D. -/

namespace CSPConsequence.RuntimeMetadata

open Groundwork QuerySizes

theorem metadata {k g b Δ K E : ℕ} (hk : 1 ≤ k) (hE : 1 ≤ E)
    (hkE : k ≤ E) (hgE : g ≤ E) (hbE : b ≤ E) (hKE : K ≤ E) :
    let P := Δ*b*(k/g+1)
    let B := (k/g+1)+(k/g+1)*(k/g+1)+1
    P ≤ 2*Δ*E^2 ∧ B ≤ 7*E^2 ∧
      g*(P+B) ≤ (2*Δ+7)*E^3 ∧
      g*(P+B)+size (1,2*K) ≤ (2*Δ+12)*E^3 := by
  intro P B
  have hp : P ≤ 2*Δ*E^2 := by
    calc
      _ ≤ 2*Δ*b*k := CostParameters.row_bound hk
      _ ≤ 2*Δ*E*E := Nat.mul_le_mul (Nat.mul_le_mul_left _ hbE) hkE
      _ = _ := by ring
  have hB : B ≤ 7*E^2 :=
    (CostParameters.entry_bound hk).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hkE 2))
  have hV : g*(P+B) ≤ (2*Δ+7)*E^3 := by
    calc
      _ ≤ E*(2*Δ*E^2+7*E^2) := Nat.mul_le_mul hgE (Nat.add_le_add hp hB)
      _ = _ := by ring
  have hz : size (1,2*K) ≤ 2*K+3 := by
    simp only [size_prod,size_nat]
    have hsz : Nat.size (2*K) ≤ 2*K := Nat.size_le.mpr Nat.lt_two_pow_self
    have hone : Nat.size 1 = 1 := by decide
    rw [hone]
    omega
  have hE3 : E ≤ E^3 := le_self_pow hE (by decide)
  have hzE : size (1,2*K) ≤ 5*E^3 := by omega
  exact ⟨hp,hB,hV,by nlinarith⟩

theorem state_bound {C : Type} [HasSize C] (c : C)
    (k g b Δ K C₁ 𝒯 E : ℕ) (hk : 1 ≤ k) (hE : 1 ≤ E)
    (hkE : k ≤ E) (hgE : g ≤ E) (hbE : b ≤ E) (hKE : K ≤ E)
    (hc : size c ≤ 10*E) :
    let P := Δ*b*(k/g+1)
    let B := (k/g+1)+(k/g+1)*(k/g+1)+1
    size c+(𝒯+(g*(P+B)+size (1,2*K))^C₁)+room c g P B+4 ≤
      ((8*Δ+45)+(2*Δ+12)^C₁)*E^(3*C₁+2)+𝒯 := by
  intro P B
  obtain ⟨hp,hB,hV,hW⟩ := metadata hk hE hkE hgE hbE hKE (Δ := Δ)
  change P ≤ 2*Δ*E^2 at hp
  change B ≤ 7*E^2 at hB
  change g*(P+B) ≤ (2*Δ+7)*E^3 at hV
  change g*(P+B)+size (1,2*K) ≤ (2*Δ+12)*E^3 at hW
  have hE2 : E ≤ E^2 := le_self_pow hE (by decide)
  have hE21 : 1 ≤ E^2 := one_le_pow₀ hE
  have hbody : 2*size c+2*g+4*P+B+16 ≤ (8*Δ+45)*E^2 := by
    nlinarith
  have hpower : (g*(P+B)+size (1,2*K))^C₁ ≤ (2*Δ+12)^C₁*E^(3*C₁) := by
    have hh := Nat.pow_le_pow_left hW C₁
    simpa only [mul_pow,← pow_mul] using hh
  have hsmall := Nat.pow_le_pow_right hE (by omega : 2 ≤ 3*C₁+2)
  have hbig := Nat.pow_le_pow_right hE (by omega : 3*C₁ ≤ 3*C₁+2)
  have hh1 := Nat.mul_le_mul_left (8*Δ+45) hsmall
  have hh2 := Nat.mul_le_mul_left ((2*Δ+12)^C₁) hbig
  unfold room
  nlinarith

#print axioms metadata
#print axioms state_bound

end CSPConsequence.RuntimeMetadata
