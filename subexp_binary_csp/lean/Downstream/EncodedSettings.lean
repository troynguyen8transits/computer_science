import Downstream.CSPBounds
import Downstream.FiniteEncoding

set_option autoImplicit false

/-! Instantiate the concrete block codec on actual merged CSP settings.
This file transports the finite sum. It does not assert the bit-network
factorization or a query-machine complexity bound.
-/

namespace CSPConsequence.EncodedSettings

open Finset Groundwork DomainCodec

def members {k g : ℕ} (χ : Fin k → Fin g) (G : Fin g) : List (Fin k) :=
  (List.finRange k).filter fun a => χ a == G

theorem mem_members {k g : ℕ} (χ : Fin k → Fin g) (G : Fin g) (a : Fin k) :
    a ∈ members χ G ↔ χ a = G := by simp [members]

theorem nodup_members {k g : ℕ} (χ : Fin k → Fin g) (G : Fin g) :
    (members χ G).Nodup := (List.nodup_finRange k).filter _

variable {k D g : ℕ} (I : Instance k D) (d : Fin D) (b : ℕ)
  (χ : Fin k → Fin g)

theorem settings_eq (G : Fin g) :
    ((I.network d b).merge χ d d).S G = assignments d (members χ G) := by
  change tuples (fun a => χ a = G) (fun _ => univ) d =
    tuples (fun a => a ∈ members χ G) (fun _ => univ) d
  simp only [mem_members]

theorem encode_mem (hD : D ≤ 2^b) (G : Fin g)
    (z : Fin k → Fin D) :
    encode b (members χ G) z ∈ encodedStates D b (members χ G) :=
  (mem_encodedStates b _ _).mpr (encode_legal _ (nodup_members χ G) z hD)

theorem decode_mem_settings (G : Fin g) (w : List Bool) :
    decode d b (members χ G) w ∈ ((I.network d b).merge χ d d).S G := by
  rw [settings_eq]
  exact decode_mem d b _ w

theorem settings_roundtrip (hD : D ≤ 2^b) (G : Fin g)
    (z : Fin k → Fin D) (hz : z ∈ ((I.network d b).merge χ d d).S G) :
    decode d b (members χ G) (encode b (members χ G) z) = z := by
  rw [settings_eq] at hz
  exact decode_encode_assignment d _ (nodup_members χ G) hD z hz

theorem words_roundtrip (G : Fin g) (w : List Bool)
    (hw : w ∈ encodedStates D b (members χ G)) :
    encode b (members χ G) (decode d b (members χ G) w) = w :=
  encode_decode d _ (nodup_members χ G) w ((mem_encodedStates b _ w).mp hw)

/-- Every summand may depend on all groups; the codec still preserves the whole sum. -/
theorem sum_settings (hD : D ≤ 2^b) (F : (Fin g → Fin k → Fin D) → ℤ) :
    (∑ w ∈ Fintype.piFinset (fun G => encodedStates D b (members χ G)),
      F (fun G => decode d b (members χ G) (w G))) =
    ∑ z ∈ Fintype.piFinset ((I.network d b).merge χ d d).S, F z := by
  classical
  let dec := fun w : Fin g → List Bool => fun G => decode d b (members χ G) (w G)
  let enc := fun z : Fin g → Fin k → Fin D => fun G => encode b (members χ G) (z G)
  apply Finset.sum_nbij dec
  · intro w _
    exact Fintype.mem_piFinset.mpr fun G => decode_mem_settings I d b χ G (w G)
  · intro w hw w' hw' heq
    funext G
    have h := congrArg (fun z => encode b (members χ G) (z G)) heq
    change encode b (members χ G) (decode d b (members χ G) (w G)) =
      encode b (members χ G) (decode d b (members χ G) (w' G)) at h
    rwa [words_roundtrip d b χ G (w G) (Fintype.mem_piFinset.mp hw G),
      words_roundtrip d b χ G (w' G) (Fintype.mem_piFinset.mp hw' G)] at h
  · intro z hz
    refine ⟨enc z, Fintype.mem_piFinset.mpr (fun G => encode_mem b χ hD G (z G)), ?_⟩
    funext G
    exact settings_roundtrip I d b χ hD G (z G) (Fintype.mem_piFinset.mp hz G)
  · intro _ _
    rfl

/-- The CSP count itself, summed over legal bit strings at the actual groups. -/
theorem count_as_bits (hD : D ≤ 2^b) :
    (∑ w ∈ Fintype.piFinset (fun G => encodedStates D b (members χ G)),
      (∏ G, ((I.network d b).merge χ d d).W G
        (decode d b (members χ G) (w G))) *
      ∏ p ∈ pairs (Fin g), ((I.network d b).merge χ d d).Ψ p.1 p.2
        (decode d b (members χ p.1) (w p.1))
        (decode d b (members χ p.2) (w p.2))) = (I.count : ℤ) := by
  calc
    _ = ((I.network d b).merge χ d d).value := sum_settings I d b χ hD _
    _ = (I.count : ℤ) := I.coarsened_count d b χ

#print axioms settings_roundtrip
#print axioms words_roundtrip
#print axioms sum_settings
#print axioms count_as_bits

end CSPConsequence.EncodedSettings
