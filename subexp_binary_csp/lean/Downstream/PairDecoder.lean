import Downstream.ProviderTables

set_option autoImplicit false

/-! Polynomial-time label decoding at ordered vertex-pair indices, with an
exact connection to the existing typed label decoder on every input string.
-/

namespace CSPConsequence.PairDecoder

open Groundwork DomainCodec

abbrev PairBlockInput := ℕ × (List (ℕ × ℕ) × (List Bool × (ℕ × ℕ)))

def readPairBlock (p : PairBlockInput) : List Bool :=
  (chunks (p.2.1.map fun _ => p.1) p.2.2.1).getD (p.2.1.idxOf p.2.2.2) []

@[fun_prop] theorem readPairBlock_polyT : PolyT readPairBlock := by
  unfold readPairBlock
  fun_prop

def decodePairNat (p : ℕ × PairBlockInput) : ℕ :=
  if p.2.2.2.2 ∈ p.2.2.1 then
    let n := ofWord (readPairBlock p.2)
    if n < p.1 then n else 0
  else 0

@[fun_prop] theorem decodePairNat_polyT : PolyT decodePairNat := by
  unfold decodePairNat
  dsimp only
  fun_prop

theorem idxOf_map_injective {α β : Type} [DecidableEq α] [DecidableEq β]
    [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (f : α → β) (hf : Function.Injective f) (e : List α) (a : α) :
    (e.map f).idxOf (f a) = e.idxOf a := by
  induction e with
  | nil => rfl
  | cons v e ih =>
    by_cases h : v = a
    · subst v
      simp
    · have hv : f v ≠ f a := fun hv => h (hf hv)
      simp [h, hv, ih]

theorem mem_map_injective {α β : Type} (f : α → β) (hf : Function.Injective f)
    (e : List α) (a : α) : f a ∈ e.map f ↔ a ∈ e := by
  constructor
  · intro ha
    obtain ⟨v,hv,heq⟩ := List.mem_map.mp ha
    simpa [hf heq] using hv
  · intro ha
    exact List.mem_map.mpr ⟨a,ha,rfl⟩

def pairValues {k : ℕ} (p : Fin k × Fin k) : ℕ × ℕ := (p.1.val,p.2.val)

theorem pairValues_injective (k : ℕ) : Function.Injective (pairValues (k := k)) := by
  intro p q h
  exact Prod.ext (Fin.ext (congrArg Prod.fst h)) (Fin.ext (congrArg Prod.snd h))

theorem readPairBlock_eq {k : ℕ} (b : ℕ) (e : List (Fin k × Fin k))
    (w : List Bool) (a : Fin k × Fin k) :
    readPairBlock (b,e.map pairValues,w,pairValues a) = cut (fun _ => b) [] e w a := by
  rw [readPairBlock, cut_eq_getD_beq, idxOf_map_injective pairValues (pairValues_injective k)]
  simp [List.map_map, Function.comp_def]

theorem decodePairNat_eq {k D : ℕ} (hD : 0 < D) (b : ℕ)
    (e : List (Fin k × Fin k)) (w : List Bool) (a : Fin k × Fin k) :
    decodePairNat (D,b,e.map pairValues,w,pairValues a) =
      (DomainCodec.decode ⟨0,hD⟩ b e w a).val := by
  unfold decodePairNat DomainCodec.decode
  simp only [mem_map_injective pairValues (pairValues_injective k), readPairBlock_eq]
  by_cases ha : a ∈ e
  · simp only [if_pos ha]
    unfold decodeValue
    split_ifs <;> rfl
  · simp [ha]

#print axioms readPairBlock_polyT
#print axioms decodePairNat_polyT
#print axioms decodePairNat_eq

end CSPConsequence.PairDecoder
