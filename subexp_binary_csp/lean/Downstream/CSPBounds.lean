import Downstream.BalancedCSP

set_option autoImplicit false

/-! Bounds on actual integer network entries after coarsening.
Directly applies Anthropic's general merge_sized theorem. The resulting
height grows polynomially with group size and is sufficient for the planned
time bound; it is not assumed to stay constant through arbitrary merges.
-/

namespace CSPConsequence.Instance

open Finset Groundwork

variable {k D : ℕ} (I : CSPConsequence.Instance k D)

theorem sized (d : Fin D) {b Δ : ℕ} (hb : 1 ≤ b) (hD : D ≤ 2^b)
    (hΔ : 1 ≤ Δ) (hdeg : ∀ a, I.degree a ≤ Δ) :
    (I.network d b).Sized (Δ*b) 1 := by
  refine { I.shaped d hb hD hΔ hdeg with
    abs_W := ?_, abs_f := ?_, abs_Ψ := ?_ }
  · intro a z
    norm_num [network]
  · intro a v z θ
    simp only [network]
    split_ifs <;> norm_num
  · intro a v x y hav
    rcases lt_or_gt_of_ne hav with hav | hva
    · rw [I.interaction d b a v hav]
      split_ifs <;> norm_num
    · rw [Network.Ψ_comm, I.interaction d b v a hva]
      split_ifs <;> norm_num

theorem balanced_sized {g b Δ : ℕ} (d : Fin D) (hg : 0 < g) (hb : 1 ≤ b)
    (hD : D ≤ 2^b) (hΔ : 1 ≤ Δ) (hdeg : ∀ a, I.degree a ≤ Δ) :
    ((I.network d b).merge (balanced hg) d d).Sized
      (Δ*b*(k/g+1)) ((k/g+1)+(k/g+1)*(k/g+1)) := by
  simpa only [one_mul] using Network.merge_sized (I.network d b)
    (balanced hg) d d (I.sized d hb hD hΔ hdeg) (balanced_fiber hg)

#print axioms sized
#print axioms balanced_sized

end CSPConsequence.Instance
