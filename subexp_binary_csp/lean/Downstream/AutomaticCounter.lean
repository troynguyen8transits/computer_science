import Downstream.FinitePreparation
import Downstream.BitInputMachine

set_option autoImplicit false
set_option maxHeartbeats 3000000

/-! The native fast branch chooses its level, group count and domain bit width
itself. The canonical external input has zeroes in all three advice headers;
their decoded values are discarded. Total fallback composition is separate. -/

namespace CSPConsequence.AutomaticCounter

open Groundwork Printed Turing NodeRefinement QuerySizes

def canonicalInput {k D : ℕ} (I : Instance k D) : List Bool :=
  BitInputCodec.encode (paramsOf I 0 0,unary 0)

def wordMachine {Δ : ℕ} (c : CounterExistence.Counter Δ) : Stepped (List Bool) (List Bool) :=
  Stepped.mapOut (Stepped.mapIn
    (fun w => FinitePreparation.prepare c.kf (BitInputCodec.decode w).1.1) c.machine)
    BitInputMachine.outputBits

theorem wordMachine_poly {Δ : ℕ} (c : CounterExistence.Counter Δ) :
    Nonempty (IsPolyT (wordMachine c)) := by
  obtain ⟨hM⟩ := c.poly
  letI : IsPolyT c.machine := hM
  have hp := FinitePreparation.prepare_polyT c.kf c.computes.1
  have hprep : PolyT (fun w : List Bool =>
      FinitePreparation.prepare c.kf (BitInputCodec.decode w).1.1) :=
    hp.comp (by fun_prop)
  letI : IsPolyT (Stepped.mapIn
      (fun w => FinitePreparation.prepare c.kf (BitInputCodec.decode w).1.1) c.machine) :=
    IsPolyT.mapIn hprep
  exact ⟨IsPolyT.mapOut BitInputMachine.outputBits_polyT⟩

theorem wordMachine_runs {Δ k D : ℕ} (c : CounterExistence.Counter Δ)
    (I : Instance k D) (hlarge : c.K 0^32 ≤ k)
    {T S : ℕ}
    (h : c.machine.Runs
      (paramsOf I (3*(c.K (LevelSelection.select c.K k))^8) (Nat.size D),
        unary (c.K (LevelSelection.select c.K k))) T S (I.count:ℤ)) :
    (wordMachine c).Runs (canonicalInput I) T S (Nat.bits I.count) := by
  have hin : FinitePreparation.prepare c.kf (BitInputCodec.decode (canonicalInput I)).1.1 =
      (paramsOf I (3*(c.K (LevelSelection.select c.K k))^8) (Nat.size D),
        unary (c.K (LevelSelection.select c.K k))) := by
    unfold canonicalInput
    rw [BitInputCodec.decode_encode _ (BitInputCodec.rectangular_paramsOf I 0 0 0)]
    exact FinitePreparation.prepare_of c.kf c.computes (c.levels.K_two 0) c.levels.K_lt I hlarge
  unfold wordMachine
  have hh := Stepped.mapOut_runs (f := BitInputMachine.outputBits)
    (Stepped.mapIn_runs (f := fun w : List Bool =>
      FinitePreparation.prepare c.kf (BitInputCodec.decode w).1.1)
      (a := canonicalInput I) (hin.symm ▸ h))
  simpa only [BitInputMachine.outputBits,Int.toNat_natCast] using hh

/-- One native machine and simulation exponent before all CSP inputs. This
large-input branch takes no unproved clique or counter algorithm as input. -/
theorem exists_native (Δ : ℕ) :
    ∃ (c : CounterExistence.Counter Δ) (N : TM2ComputableAux Bool Bool) (q : ℕ),
      (∀ i, Finite (N.tm.Γ i)) ∧
      ∀ {k D : ℕ} (I : Instance k D) (hlarge : c.K 0^32 ≤ k)
        (hpos : 0 < D) (hΔ : 1 ≤ Δ) (hdeg : ∀ a, I.degree a ≤ Δ),
        let l := LevelSelection.select c.K k
        let K := c.K l
        let g := 3*K^8
        let b := Nat.size D
        let P := Δ*b*(k/g+1)
        let B := (k/g+1)+(k/g+1)*(k/g+1)+1
        let hg : 0 < g := by
          have hK := c.levels.K_two l
          dsimp [g]
          positivity
        let 𝒯 := LevelCounter.budget (c.e l) c.C₀ K g P B
          (BitNetwork.data I ⟨0,hpos⟩ b (balanced hg)).U
        ∃ (T S : ℕ),
          Nonempty (TM2OutputsInTime N.tm ((canonicalInput I).map N.inputAlphabet.invFun)
            (some ((Nat.bits I.count).map N.outputAlphabet.invFun))
            (q*(3*T+1)*((canonicalInput I).length+S+1)^q)) ∧
          S = size (paramsOf I g b)+(𝒯+(g*(P+B)+size (1,2*K))^c.C₁)+
            room (paramsOf I g b) g P B+4 ∧
          (T:ℝ) ≤ ((K:ℝ)^g+𝒯*(2:ℝ)^(2*(g:ℝ)*P/K))*((g:ℝ)*(P+B))^c.C₁ := by
  obtain ⟨c⟩ := CounterExistence.exists_counter Δ
  obtain ⟨hpoly⟩ := wordMachine_poly c
  letI : IsPolyT (wordMachine c) := hpoly
  obtain ⟨N,q,hfin,hhost⟩ := CountKSat.exists_tmW (wordMachine c)
  refine ⟨c,N,q,hfin,?_⟩
  intro k D I hlarge hpos hΔ hdeg l K g b P B hg 𝒯
  have hK : 2 ≤ K := c.levels.K_two l
  have hg2 : 2 ≤ g := by
    have hp : 1 ≤ K^8 := one_le_pow₀ (by omega : 1 ≤ K)
    dsimp [g]
    omega
  obtain ⟨T,hr,ht⟩ := c.correct I b l hg hpos
    (FinitePreparation.bitWidth_pos hpos) FinitePreparation.bitWidth_capacity hΔ hdeg hg2 rfl
  have hw := wordMachine_runs c I hlarge hr
  exact ⟨T,_,hhost _ _ _ _ hw,rfl,ht⟩

#print axioms wordMachine_poly
#print axioms wordMachine_runs
#print axioms exists_native

end CSPConsequence.AutomaticCounter
