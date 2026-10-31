import Downstream.ProviderMetadata
import Downstream.FactorRefinement
import Downstream.QuerySizes

set_option autoImplicit false

/-! The actual finite-input provider satisfies the algorithm's Give/Keeps
interface with one abstract step per query, separately certified polynomial
native implementation, and an explicit common state-size bound.
-/

namespace CSPConsequence.ProviderGive

open Groundwork Finset DomainCodec ProviderParameters ProviderTables ProviderLabels
  NodeRefinement TableRefinement LabelRefinement FactorRefinement ProviderMetadata QuerySizes

variable {k D g : ℕ} (I : Instance k D) (b Δ : ℕ) (hg : 0 < g)
  (hpos : 0 < D) (hb : 1 ≤ b) (hD : D ≤ 2^b) (hΔ : 1 ≤ Δ)
  (hdeg : ∀ a, I.degree a ≤ Δ)

include hb hD hΔ hdeg

theorem cap_of (G H : Fin g) : (procs Δ).cap (paramsOf I g b) G.val H.val =
    (BitNetwork.data I ⟨0,hpos⟩ b (balanced hg)).c G H := by
  let χ := balanced (k := k) hg
  let N := BitNetwork.data I ⟨0,hpos⟩ b χ
  have hn : N.Is (Δ*b*(k/g+1)) ((k/g+1)+(k/g+1)*(k/g+1)+1) :=
    BitNetwork.is_valid I ⟨0,hpos⟩ hg hb hD hΔ hdeg
  have hm : N.c (min G H) (max G H) = N.c G H := by
    rcases le_total G H with h | h
    · simp [min_eq_left h, max_eq_right h]
    · simpa [min_eq_right h, max_eq_left h] using hn.c_symm H G
  calc
    _ = b*(BitNetwork.labels I χ G H).length := by
      change blockWidth (paramsOf I g b)*(crossingPairs (paramsOf I g b,(G.val,H.val))).length = _
      rw [crossingPairs_of I b hg G H]
      simp [paramsOf, blockWidth, χ]
    _ = N.c (min G H) (max G H) :=
      (BitNetwork.label_capacity I ⟨0,hpos⟩ b χ (min G H) (max G H)).symm
    _ = N.c G H := hm

theorem gives :
    (procs Δ).Give (paramsOf I g b) (BitNetwork.data I ⟨0,hpos⟩ b (balanced hg))
      (Δ*b*(k/g+1)) ((k/g+1)+(k/g+1)*(k/g+1)+1) 1
      (room (paramsOf I g b) g (Δ*b*(k/g+1)) ((k/g+1)+(k/g+1)*(k/g+1)+1)) := by
  let c := paramsOf I g b
  let N := BitNetwork.data I ⟨0,hpos⟩ b (balanced hg)
  let P := Δ*b*(k/g+1)
  let B := (k/g+1)+(k/g+1)*(k/g+1)+1
  have hn : N.Is P B := BitNetwork.is_valid I ⟨0,hpos⟩ hg hb hD hΔ hdeg
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact P_of I b Δ
  · exact B_of I b Δ
  · intro a
    exact len_of I ⟨0,hpos⟩ b Δ hg a
  · intro a v _
    exact cap_of I b Δ hg hpos hb hD hΔ hdeg a v
  · intro a w hw
    exact (memMachine_correct I b hg hpos a w).mono le_rfl
      (mem_room c a w (hw.le.trans (hn.len_le a)) _)
  · intro a w hw
    exact (weightMachine_correct I b hg hpos a w).mono le_rfl
      (one_room c a w ((hn.len_S a w hw).le.trans (hn.len_le a)) _ (hn.ii_W a w hw))
  · intro a v hne w hw w' hw'
    exact (interactionMachine_correct I b hg hpos a v hne w w').mono le_rfl
      (two_room c a v w w' ((hn.len_S a w hw).le.trans (hn.len_le a))
        ((hn.len_S v w' hw').le.trans (hn.len_le v)) _ (hn.ii_Ψ a v hne w hw w' hw'))
  · intro a v hne w hw θ hθ
    have hθlen : θ.length ≤ P := (mem_words.mp hθ).le.trans (capacity_le N hn a v hne)
    exact (factorMachine_correct I b hg hpos a v w θ).mono le_rfl
      (two_room c a v w θ ((hn.len_S a w hw).le.trans (hn.len_le a)) hθlen _
        (hn.ii_f a v hne w hw θ hθ))

theorem isNetwork :
    Eight.SecNetworks.IsNetwork (procs Δ) (paramsOf I g b)
      (BitNetwork.data I ⟨0,hpos⟩ b (balanced hg)) (Δ*b*(k/g+1))
      ((k/g+1)+(k/g+1)*(k/g+1)+1) 1
      (room (paramsOf I g b) g (Δ*b*(k/g+1)) ((k/g+1)+(k/g+1)*(k/g+1)+1)) :=
  ⟨BitNetwork.is_valid I ⟨0,hpos⟩ hg hb hD hΔ hdeg, by decide,
    gives I b Δ hg hpos hb hD hΔ hdeg⟩

#print axioms gives
#print axioms isNetwork
#print axioms ProviderMetadata.procs_keeps

end CSPConsequence.ProviderGive
