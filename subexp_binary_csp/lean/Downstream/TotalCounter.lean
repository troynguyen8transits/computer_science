import Downstream.AutomaticCounter
import Downstream.DegreeGuard
import Downstream.BruteCSPMachine

set_option autoImplicit false
set_option maxHeartbeats 3000000

/-! One total counter on canonical finite CSP inputs. A certified degree/size
guard selects the fast branch; all remaining inputs use the verified fallback.
This supplies global correctness without a degree or nonempty-domain promise.
The quantitative native bound on the fast branch is composed separately. -/

namespace CSPConsequence.TotalCounter

open Groundwork Printed FiniteInput NodeRefinement Turing

def eligible {Δ : ℕ} (c : CounterExistence.Counter Δ) (input : Input) : Bool :=
  decide (c.K 0^32 ≤ vertices input) && decide (2 ≤ domain input) && DegreeGuard.check Δ input

@[fun_prop] theorem eligible_polyT {Δ : ℕ} (c : CounterExistence.Counter Δ) :
    PolyT (eligible c) := by
  unfold eligible vertices domain
  fun_prop

theorem eligible_of {Δ k D : ℕ} (c : CounterExistence.Counter Δ) (I : Instance k D) :
    eligible c (tabulate I) = true ↔
      c.K 0^32 ≤ k ∧ 2 ≤ D ∧ ∀ a, I.degree a ≤ Δ := by
  simp only [eligible,Bool.and_eq_true,decide_eq_true_eq,vertices_tabulate,domain_tabulate,
    DegreeGuard.check_of]
  tauto

def fast {Δ : ℕ} (c : CounterExistence.Counter Δ) : Stepped Input ℤ :=
  Stepped.mapIn (FinitePreparation.prepare c.kf) c.machine

def fallbackWidth (input : Input) : ℕ :=
  if domain input ≤ 1 then 0 else FinitePreparation.bitWidth input

theorem fallbackWidth_capacity (D : ℕ) :
    D ≤ 2^(if D ≤ 1 then 0 else Nat.size D) := by
  by_cases h : D ≤ 1
  · simpa only [if_pos h,pow_zero] using h
  · simpa only [if_neg h] using (FinitePreparation.bitWidth_capacity (D := D))

def fallbackInput (input : Input) : ProviderParameters.Params :=
  (input,[()],unary (fallbackWidth input))

@[fun_prop] theorem fallbackInput_polyT : PolyT fallbackInput := by
  have hb := FinitePreparation.bitWidth_unary
  have hw : Groundwork.Unary fallbackWidth := by
    unfold fallbackWidth domain
    fun_prop
  exact PolyT.prodMk (by fun_prop) (PolyT.prodMk (by fun_prop) hw)

def fallback : Stepped Input ℤ := Stepped.mapIn fallbackInput BruteCSP.machine

def machine {Δ : ℕ} (c : CounterExistence.Counter Δ) : Stepped Input ℤ :=
  Stepped.ite (eligible c) (fast c) fallback

theorem machine_poly {Δ : ℕ} (c : CounterExistence.Counter Δ) :
    Nonempty (IsPolyT (machine c)) := by
  obtain ⟨hc⟩ := c.poly
  letI : IsPolyT c.machine := hc
  letI : IsPolyT (fast c) := IsPolyT.mapIn (FinitePreparation.prepare_polyT c.kf c.computes.1)
  letI : IsPolyT BruteCSP.machine := BruteCSP.machine_poly
  letI : IsPolyT fallback := IsPolyT.mapIn fallbackInput_polyT
  exact ⟨IsPolyT.ite (eligible_polyT c)⟩

theorem fast_runs {Δ k D T S : ℕ} (c : CounterExistence.Counter Δ)
    (I : Instance k D) (hlarge : c.K 0^32 ≤ k)
    (h : c.machine.Runs
      (paramsOf I (3*(c.K (LevelSelection.select c.K k))^8) (Nat.size D),
        unary (c.K (LevelSelection.select c.K k))) T S (I.count:ℤ)) :
    (fast c).Runs (tabulate I) T S (I.count:ℤ) := by
  apply Stepped.mapIn_runs
  rw [FinitePreparation.prepare_of c.kf c.computes (c.levels.K_two 0) c.levels.K_lt I hlarge]
  exact h

theorem fast_branch_runs {Δ k D T S : ℕ} (c : CounterExistence.Counter Δ)
    (I : Instance k D) (hlarge : c.K 0^32 ≤ k) (hD : 2 ≤ D)
    (hdeg : ∀ a, I.degree a ≤ Δ)
    (h : c.machine.Runs
      (paramsOf I (3*(c.K (LevelSelection.select c.K k))^8) (Nat.size D),
        unary (c.K (LevelSelection.select c.K k))) T S (I.count:ℤ)) :
    (machine c).Runs (tabulate I) T (S+1) (I.count:ℤ) :=
  Stepped.ite_runs_true ((eligible_of c I).mpr ⟨hlarge,hD,hdeg⟩) (fast_runs c I hlarge h)

theorem correct {Δ k D : ℕ} (c : CounterExistence.Counter Δ) (hΔ : 1 ≤ Δ)
    (I : Instance k D) : ∃ T S, (machine c).Runs (tabulate I) T S (I.count:ℤ) := by
  by_cases he : eligible c (tabulate I) = true
  · obtain ⟨hlarge,hD,hdeg⟩ := (eligible_of c I).mp he
    have hpos : 0 < D := by omega
    let l := LevelSelection.select c.K k
    let K := c.K l
    let g := 3*K^8
    have hK : 2 ≤ K := c.levels.K_two l
    have hg2 : 2 ≤ g := by
      have hp : 1 ≤ K^8 := one_le_pow₀ (by omega : 1 ≤ K)
      dsimp [g]
      omega
    have hg : 0 < g := by omega
    obtain ⟨T,hr,ht⟩ := c.correct I (Nat.size D) l hg hpos
      (FinitePreparation.bitWidth_pos hpos) FinitePreparation.bitWidth_capacity hΔ hdeg hg2 rfl
    exact ⟨_,_,Stepped.ite_runs_true he (fast_runs c I hlarge hr)⟩
  · let b := if D ≤ 1 then 0 else Nat.size D
    have hf := BruteCSP.machine_correct I 1 b (fallbackWidth_capacity D)
    have hin : fallbackInput (tabulate I) = paramsOf I 1 b := by
      simp [fallbackInput,fallbackWidth,FinitePreparation.bitWidth,paramsOf,domain_tabulate,unary,b]
    have hr : fallback.Runs (tabulate I) (2*BruteCSP.bound (paramsOf I 1 b))
        (2*size (paramsOf I 1 b)+3*BruteCSP.width (paramsOf I 1 b)+12) (I.count:ℤ) := by
      apply Stepped.mapIn_runs
      rw [hin]
      exact hf
    exact ⟨_,_,Stepped.ite_runs_false (Bool.eq_false_iff.mpr he) hr⟩

def wordMachine {Δ : ℕ} (c : CounterExistence.Counter Δ) : Stepped (List Bool) (List Bool) :=
  Stepped.mapOut (Stepped.mapIn (fun w => (BitInputCodec.decode w).1.1) (machine c))
    BitInputMachine.outputBits

theorem wordMachine_poly {Δ : ℕ} (c : CounterExistence.Counter Δ) :
    Nonempty (IsPolyT (wordMachine c)) := by
  obtain ⟨hm⟩ := machine_poly c
  letI : IsPolyT (machine c) := hm
  letI : IsPolyT (Stepped.mapIn (fun w => (BitInputCodec.decode w).1.1) (machine c)) :=
    IsPolyT.mapIn (by fun_prop)
  exact ⟨IsPolyT.mapOut BitInputMachine.outputBits_polyT⟩

theorem native_from_runs {Δ : ℕ} (c : CounterExistence.Counter Δ) :
    ∃ (N : TM2ComputableAux Bool Bool) (q : ℕ), (∀ i, Finite (N.tm.Γ i)) ∧
      ∀ {k D : ℕ} (I : Instance k D) (T S : ℕ), (machine c).Runs (tabulate I) T S (I.count:ℤ) →
        Nonempty (TM2OutputsInTime N.tm
          ((AutomaticCounter.canonicalInput I).map N.inputAlphabet.invFun)
          (some ((Nat.bits I.count).map N.outputAlphabet.invFun))
          (q*(T+1)*((AutomaticCounter.canonicalInput I).length+S+1)^q)) := by
  obtain ⟨hm⟩ := wordMachine_poly c
  letI : IsPolyT (wordMachine c) := hm
  obtain ⟨N,q,hfin,hhost⟩ := CountKSat.exists_tmW (wordMachine c)
  refine ⟨N,q,hfin,?_⟩
  intro k D I T S hr
  have hin : (BitInputCodec.decode (AutomaticCounter.canonicalInput I)).1.1 = tabulate I := by
    unfold AutomaticCounter.canonicalInput
    rw [BitInputCodec.decode_encode _ (BitInputCodec.rectangular_paramsOf I 0 0 0)]
    rfl
  have hi : (machine c).Runs (BitInputCodec.decode (AutomaticCounter.canonicalInput I)).1.1
      T S (I.count:ℤ) := hin.symm ▸ hr
  have hw := Stepped.mapOut_runs (f := BitInputMachine.outputBits)
    (Stepped.mapIn_runs (f := fun w : List Bool => (BitInputCodec.decode w).1.1) hi)
  have hout : (wordMachine c).Runs (AutomaticCounter.canonicalInput I) T S (Nat.bits I.count) := by
    simpa only [wordMachine,BitInputMachine.outputBits,Int.toNat_natCast] using hw
  exact hhost _ _ _ _ hout

theorem native_total (Δ : ℕ) (hΔ : 1 ≤ Δ) :
    ∃ (N : TM2ComputableAux Bool Bool) (q : ℕ), (∀ i, Finite (N.tm.Γ i)) ∧
      ∀ {k D : ℕ} (I : Instance k D), ∃ T S,
        Nonempty (TM2OutputsInTime N.tm
          ((AutomaticCounter.canonicalInput I).map N.inputAlphabet.invFun)
          (some ((Nat.bits I.count).map N.outputAlphabet.invFun))
          (q*(T+1)*((AutomaticCounter.canonicalInput I).length+S+1)^q)) := by
  obtain ⟨c⟩ := CounterExistence.exists_counter Δ
  obtain ⟨N,q,hfin,hhost⟩ := native_from_runs c
  refine ⟨N,q,hfin,?_⟩
  intro k D I
  obtain ⟨T,S,hr⟩ := correct c hΔ I
  exact ⟨T,S,hhost I T S hr⟩

#print axioms machine_poly
#print axioms correct
#print axioms fast_branch_runs
#print axioms native_from_runs
#print axioms native_total

end CSPConsequence.TotalCounter
