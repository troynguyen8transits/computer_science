import Downstream.BitNetworkValidity

set_option autoImplicit false

/-! Direct table formulas. The semantic interaction sums over exponentially many
crossing labels; a provider must instead use the equivalent product of original
relations. These definitions use only products indexed by original vertex pairs.
Correctness is proved here; the concrete input representation and polynomial-time
query-machine certificates remain separate.
-/

namespace CSPConsequence.BitNetwork

open Finset Groundwork DomainCodec

variable {k D g : ℕ} (I : Instance k D) (d : Fin D) (b : ℕ)
  (χ : Fin k → Fin g)

def relationValue (a v : Fin k) (x y : Fin D) : ℤ :=
  if I.edge a v then (if I.accepts a v x y then 1 else 0) else 1

theorem base_interaction (a v : Fin k) (hne : a ≠ v) (x y : Fin D) :
    (I.network d b).Ψ a v x y = relationValue I a v x y := by
  rcases lt_or_gt_of_ne hne with hav | hva
  · rw [I.interaction d b a v hav]
    simp [relationValue, Instance.accepts, hav]
  · rw [Network.Ψ_comm, I.interaction d b v a hva]
    simp [relationValue, Instance.accepts, hva.not_gt, I.symmetric v a]

def fastWeight (G : Fin g) (w : List Bool) : ℤ :=
  ∏ p ∈ (pairs (Fin k)).filter (fun p => χ p.1 = G ∧ χ p.2 = G),
    relationValue I p.1 p.2
      (decode d b (EncodedSettings.members χ G) w p.1)
      (decode d b (EncodedSettings.members χ G) w p.2)

theorem fastWeight_eq (G : Fin g) (w : List Bool) :
    fastWeight I d b χ G w = (data I d b χ).W G w := by
  change _ = (∏ a ∈ univ.filter (fun a : Fin k => χ a = G), (1 : ℤ)) *
    ∏ p ∈ (pairs (Fin k)).filter (fun p => χ p.1 = G ∧ χ p.2 = G),
      (I.network d b).Ψ p.1 p.2
        (decode d b (EncodedSettings.members χ G) w p.1)
        (decode d b (EncodedSettings.members χ G) w p.2)
  simp only [prod_const_one, one_mul]
  apply Finset.prod_congr rfl
  intro p hp
  have hlt : p.1 < p.2 := (mem_filter.mp (mem_filter.mp hp).1).2
  exact (base_interaction I d b _ _ hlt.ne _ _).symm

def fastInteraction (G H : Fin g) (w w' : List Bool) : ℤ :=
  ∏ p ∈ univ.filter (fun p : Fin k × Fin k => χ p.1 = G ∧ χ p.2 = H),
    relationValue I p.1 p.2
      (decode d b (EncodedSettings.members χ G) w p.1)
      (decode d b (EncodedSettings.members χ H) w' p.2)

theorem fastInteraction_eq (G H : Fin g) (hne : G ≠ H) (w w' : List Bool) :
    fastInteraction I d b χ G H w w' = (data I d b χ).Ψ G H w w' := by
  change _ = ((I.network d b).merge χ d d).Ψ G H
    (decode d b (EncodedSettings.members χ G) w)
    (decode d b (EncodedSettings.members χ H) w')
  rw [Network.merge_Ψ _ _ _ _ hne]
  apply Finset.prod_congr rfl
  intro p hp
  have hc := (mem_filter.mp hp).2
  have hne' : p.1 ≠ p.2 := by
    intro he
    apply hne
    rw [← hc.1, he, hc.2]
  exact (base_interaction I d b _ _ hne' _ _).symm

#print axioms base_interaction
#print axioms fastWeight_eq
#print axioms fastInteraction_eq

end CSPConsequence.BitNetwork
