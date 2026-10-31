import Downstream.BitNetwork
import Mathlib.Tactic.Positivity

set_option autoImplicit false

/-! The actual bounded-degree CSP bit network satisfies the external algorithm's
mathematical input contract. This is `Net.Is`, not `IsNetwork`: the concrete
table-provider execution and native time bound remain separate obligations.
-/

namespace CSPConsequence.BitNetwork

open Finset Groundwork DomainCodec

theorem members_length {k g : ℕ} (χ : Fin k → Fin g) (G : Fin g) :
    (EncodedSettings.members χ G).length = #{a : Fin k | χ a = G} := by
  classical
  have heq : (EncodedSettings.members χ G).toFinset = univ.filter (fun a : Fin k => χ a = G) := by
    ext a
    simp [EncodedSettings.mem_members]
  rw [← List.toFinset_card_of_nodup (EncodedSettings.nodup_members χ G), heq]

theorem is_valid {k D g b Δ : ℕ} (I : Instance k D) (d : Fin D)
    (hg : 0 < g) (hb : 1 ≤ b) (hD : D ≤ 2^b) (hΔ : 1 ≤ Δ)
    (hdeg : ∀ a, I.degree a ≤ Δ) :
    (data I d b (balanced hg)).Is (Δ*b*(k/g+1))
      ((k/g+1)+(k/g+1)*(k/g+1)+1) := by
  classical
  let χ := balanced (k := k) hg
  let M := (I.network d b).merge χ d d
  let s := k/g+1
  let B := s+s*s
  have hs := I.balanced_shaped d hg hb hD hΔ hdeg
  have hm := I.balanced_sized d hg hb hD hΔ hdeg
  have hpow : (2 : ℤ)^B < 2^(B+1) := by
    have hp : (0 : ℤ) < 2^B := by positivity
    rw [pow_succ]
    nlinarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Nat.mul_pos (Nat.mul_pos hΔ hb) (Nat.succ_pos _)
  · exact Nat.succ_pos _
  · intro G w hw
    exact ((mem_encodedStates b (EncodedSettings.members χ G) w).mp hw).1
  · intro G
    change b*(EncodedSettings.members χ G).length ≤ Δ*b*s
    rw [members_length]
    exact (Nat.mul_le_mul_left b (balanced_fiber hg G)).trans
      (Nat.mul_le_mul_right s (by nlinarith : b ≤ Δ*b))
  · intro G H _ w _ w' _
    exact Network.Ψ_comm M H G _ _
  · intro G H
    exact hs.c_symm G H
  · intro G H hne w _ w' _
    rcases lt_or_gt_of_ne hne with hGH | hHG
    · exact factor_lt I d b χ hD G H hGH w w'
    · calc
        _ = (data I d b χ).Ψ H G w' w := Network.Ψ_comm M G H _ _
        _ = ∑ θ ∈ words ((data I d b χ).c H G),
            (data I d b χ).f H G w' θ * (data I d b χ).f G H w θ :=
          factor_lt I d b χ hD H G hHG w' w
        _ = _ := by
          rw [show (data I d b χ).c H G = (data I d b χ).c G H from hs.c_symm H G]
          apply Finset.sum_congr rfl
          intro θ _
          exact mul_comm _ _
  · intro G
    exact hs.sum_c G
  · intro G w _
    exact (hm.abs_W G _).trans_lt hpow
  · intro G H hne w _ w' _
    exact (hm.abs_Ψ G H _ _ hne).trans_lt hpow
  · intro G H _ w _ θ _
    change |if legalLabel (D := D) b (labels I χ G H) θ then M.f G H
      (decode d b (EncodedSettings.members χ G) w)
      (decode d b (labels I χ G H) θ) else 0| < 2^(B+1)
    split_ifs
    · exact (hm.abs_f G H _ _).trans_lt hpow
    · simp only [abs_zero]
      positivity

#print axioms is_valid

end CSPConsequence.BitNetwork
