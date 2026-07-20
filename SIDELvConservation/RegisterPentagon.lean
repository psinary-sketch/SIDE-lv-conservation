import SIDELvConservation.CouplingsAtPhi
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Prime.Basic

/-!
# The Register Pentagon — the one premise in five registers (§27.3)

**Item (iii), sitting P1 — DEFINITIONS FROZEN, STATEMENT-ONLY.** This module compiles the
STRUCTURE of the monograph's §27.3 claim — "one premise in five registers … a reader who
discharges any one of them discharges all five" — as five Prop-level *faces* arranged
around the one goal state.  It does **not** compile the equivalences between registers
(that would encode the RH-equivalence — the W-2 trap).  Every face states its register's
CONTENT; none is a `Bool`/`True` stub or a name that asserts a conclusion.

The goal state (the pentagon's centre) is the T3 bridge target, restated verbatim from
`SIDELvConservation/PinnedGoal.lean:17-19` and `T3_StepNineBridge.lean:97` at v0.6.0:
`∃ Φ : ℝ → ℂ, (∀ C ∈ 𝒞, C Φ) ∧ mellin Φ (s / 2) ≠ 0`.  It closes as `⟨Phi, h1, h2⟩`
(`T3.T3prime_shared_witness`); **h1** (`∀ C ∈ 𝒞, C Phi`) is discharged (`h1_complete_at_Phi`),
**h2** (`mellin Phi (s/2) ≠ 0`) is the one open obligation.  The five registers are five
faces of that premise.

## Cross-kernel restatements (federation rule: no Lake deps)

Two faces have their canonical statement OFF-kernel; each is restated **verbatim** here with
an attribution note and a doc-level correspondence line asserting definitional identity,
eye-verifiable at both pins.
- **R2** `Register2_conservationHypothesis` restates `ConservationBridge.ConservationHypothesis`
  from **SIDE-kernel v1.3 = 0bc21c0** (`Bridge/ConservationBridge.lean:26-29`), with its
  helper defs `is_xi_zero` (`Kernel/XiDef.lean:34-38`) and `prime_as_real`
  (`Kernel/Voice1.lean:8`) restated verbatim.  Definitional identity: eye-verifiable.
- **R1** `Register1_universalityHypothesis` restates the load-bearing hypothesis of
  `SilenceTheorem.silence_universal` from **SIDE-kernel v1.3 = 0bc21c0**
  (`Kernel/SilenceTheorem.lean`: `ConfigurationSpace` 26-28, `Interface` 33-37,
  `Interface.is_universal` 42-44).  Definitional identity: eye-verifiable.

## The edges — STATEMENT-ONLY this sitting (three explicit lists; P2+ discharges DERIVES)

**DERIVES-planned** (compiled implications; discharged in P2 by reusing existing terminals):
- `GoalState ⇐ h1 ∧ h2` — via `T3.T3prime_shared_witness` (h1 via `h1_complete_at_Phi`).
- `Register2_conservationHypothesis → RiemannHypothesis` — restated/attributed; the compiled
  witness is `ConservationBridge.riemann_hypothesis` (SIDE-kernel v1.3).
- `Register4` channel decomposition `λ_n = λ_A(n) + λ_Z(n)` — via SIDE-li-map `lam_add`
  (`73cee42`).  **Grade note: COMBINATORIAL stream-level only** (`lam : (ℕ→ℤ)→ℕ→ℤ`); the
  analytic identification of the stream with the Taylor coefficients of `log ξ` is
  **manuscript-resident**, not this edge.
- `Register5_input` certified — via `C5_input_at_Phi`.

**INTERFACES-planned** (each with its named premise as an explicit hypothesis argument, ξ-pattern):
- `Register4_positivity ↔ RiemannHypothesis` — named premise: **Li's criterion**
  (Bombieri–Lagarias 1999, via the Guinand–Weil explicit formula; **not in Mathlib**).
- `Register1_universalityHypothesis → GoalState` — named premise: the universality hypothesis.
- `Register5_output_HilbertPolya` — named premise: the Hilbert–Pólya realization.
  **DISCLAIMED**: this programme explicitly disclaims asserting it; it closes over 𝔽_q
  (Weil 1948, intersection-pairing positivity), is open over ℚ — cited, never claimed.

**NOT-COMPILED** (manuscript-resident — stated here so the absence is documented, not silent):
- **R3** `Register3_totalityThroughPlaces` — the step-(8) reflection "place-level exclusion
  reflects to mechanism level"; its native shadow is the T3 pinned `∀∃⟹∃∀` (the open `sorry`
  at `T3_StepNineBridge.lean:108`).
- **The cross-register equivalences themselves** ("discharge one → all five").  Compiling
  them would encode the RH-equivalence (the W-2 trap).  **The pentagon compiles STRUCTURE,
  never the equivalences.**

## Sorry census

This module adds **no** `sorry`.  All faces are Prop definitions; all edges are documented
above (statement-only).  The repo census stays exactly two intended sites
(`T3_StepNineBridge.lean:108`, `PinnedGoal.lean:23`).
-/

namespace SIDELvConservation
namespace RegisterPentagon

open Complex

/-! ### The goal state (pentagon centre) — verbatim from PinnedGoal.lean:17-19 / T3:97 -/

/-- The T3 bridge target: a single `Φ` witnessing every coupling in `𝒞` with non-vanishing
Mellin factor at `s/2`.  Verbatim restatement of `CombinationsExclude`
(`T3_StepNineBridge.lean:57-58`) and the `PinnedGoal`/`T3:97` goal. -/
def GoalState (𝒞 : Set T3.Coupling) (s : ℂ) : Prop :=
  ∃ Φ : ℝ → ℂ, (∀ C ∈ 𝒞, C Φ) ∧ mellin Φ (s / 2) ≠ 0

/-! ### R1 — universality hypothesis (Universal Silence Theorem)
Restated verbatim from SIDE-kernel v1.3 = 0bc21c0, `Kernel/SilenceTheorem.lean`. -/

/-- `ConfigurationSpace` — verbatim, `SilenceTheorem.lean:26-28` (SIDE-kernel v1.3). -/
structure ConfigurationSpace where
  α : Type
  nonempty : Nonempty α

/-- `Interface` — verbatim, `SilenceTheorem.lean:33-37` (SIDE-kernel v1.3). -/
structure Interface (C : ConfigurationSpace) (R : Type) where
  action : C.α → R
  essential : Prop

/-- `Interface.is_universal` — verbatim, `SilenceTheorem.lean:42-44` (SIDE-kernel v1.3):
the interface acts identically across all configurations. -/
def Interface.is_universal {C : ConfigurationSpace} {R : Type} (I : Interface C R) : Prop :=
  ∀ c₁ c₂ : C.α, I.action c₁ = I.action c₂

/-- **R1 face — the universality hypothesis.**  The load-bearing premise of
`SilenceTheorem.silence_universal` (SIDE-kernel v1.3): every essential interface is
universal.  Removing it leaves `silence_universal` with an unsolved goal (Ch. 14). -/
def Register1_universalityHypothesis : Prop :=
  ∀ (C : ConfigurationSpace) (R : Type) (I : Interface C R), I.essential → I.is_universal

/-! ### R2 — ConservationHypothesis (Route 3, multiplicative place)
Restated verbatim from SIDE-kernel v1.3 = 0bc21c0, `Bridge/ConservationBridge.lean`. -/

/-- `prime_as_real` — verbatim, `Kernel/Voice1.lean:8` (SIDE-kernel v1.3). -/
def prime_as_real (p : Nat) (_ : Nat.Prime p) : Real := (p : Real)

/-- `is_xi_zero` — verbatim, `Kernel/XiDef.lean:34-38` (SIDE-kernel v1.3): a nontrivial zero
of `riemannZeta` at real part `sigma` (excludes trivial zeros and the pole at 1). -/
def is_xi_zero (sigma : Real) : Prop :=
  Exists (fun t : Real =>
    riemannZeta (⟨sigma, t⟩ : ℂ) = 0 ∧
    (Not (Exists (fun n : Nat => (⟨sigma, t⟩ : ℂ) = -2 * (↑n + 1)))) ∧
    (⟨sigma, t⟩ : ℂ) ≠ 1)

/-- **R2 face — `ConservationHypothesis`.**  Verbatim restatement of
`ConservationBridge.ConservationHypothesis` (SIDE-kernel v1.3 = 0bc21c0,
`Bridge/ConservationBridge.lean:26-29`, existential form): every ξ-zero forces the Euler
balance equation at some prime.  Definitional identity eye-verifiable at both pins. -/
def Register2_conservationHypothesis : Prop :=
  ∀ (σ : ℝ), is_xi_zero σ →
  ∃ (p : Nat) (hp : Nat.Prime p),
  (prime_as_real p hp) ^ (-σ) = (prime_as_real p hp) ^ (-(1 - σ))

/-! ### R3 — totality of realization through places (category-shaped; NOT-COMPILED) -/

/-- **R3 face — totality through places** (step-(8) reflection): per-class exclusion at every
place reflects to combined exclusion.  Native shadow of the monograph's "if an off-line zero
existed, some mechanism would produce it, and place-level exclusion reflects to mechanism
level."  This is exactly the T3 pinned `∀∃ ⟹ ∃∀` (`T3_StepNineBridge.lean:92`, the open
`sorry` at :108) — manuscript-resident; stated here as the register's face, NOT compiled. -/
def Register3_totalityThroughPlaces (s : ℂ) : Prop :=
  (∀ C ∈ sevenClasses, T3.PerClassExcludes C s) → T3.CombinationsExclude sevenClasses s

/-! ### R4 — balance → positivity (analytic; Li's criterion)
The analytic Li coefficient stream (Taylor coefficients of `log ξ`) is manuscript-resident;
the face is stated over an abstract stream `lam : ℕ → ℝ`, honoring the two-leg split — the
combinatorial `lam_add` decomposition lives in SIDE-li-map, the analytic identification is
the manuscript premise. -/

/-- **R4 face — positivity** (Li's criterion content): the Li coefficients are non-negative.
Over the actual Taylor coefficients of `log ξ` this is RH-equivalent (Li 1997;
Bombieri–Lagarias 1999) — that identification is the named manuscript premise on the
`R4 ↔ RH` interface edge, not part of this face. -/
def Register4_positivity (lam : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → 0 ≤ lam n

/-- **R4 face, sharpest form — the channel inequality** `λ_Z(n) ≥ −λ_A(n)` between the two
independently computable channels (§27.3; BALANCE_AND_POSITIVITY).  The decomposition
`λ = λ_A + λ_Z` is compiled combinatorially (SIDE-li-map `lam_add`, `73cee42`). -/
def Register4_channelInequality (lam_A lam_Z : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → -lam_A n ≤ lam_Z n

/-! ### R5 — spectral-realization distance (input certified / output disclaimed) -/

/-- **R5 input face** — the input-stage spectral coupling: the fixed witness `Φ` is the heat
trace of a real, non-negative spectrum.  Native and CERTIFIED (`C5_input`, discharged at
`C5_input_at_Phi`).  Restated as the pentagon's R5-input face by definitional identity. -/
def Register5_input : T3.Coupling := C5_input

/-- **R5 output face — the compiled SCHEMA of the Hilbert–Pólya realization.**  Content:
there is an OPERATOR (matrix form `T : ℕ → ℕ → ℝ`), self-adjoint with respect to a
POSITIVE-DEFINITE symmetric pairing, whose diagonal spectrum realizes every nontrivial
ζ-zero.  **DISCLAIMED** — this programme explicitly disclaims asserting it; it closes over
𝔽_q (Weil 1948, Castelnuovo / intersection-pairing positivity), is open over ℚ.

Repaired from the P1 draft (reviewer screen): the earlier `0 ≤ pairing i i` + bare-spectrum
form was classically trivially true (witness `pairing ≡ 0`, choice-enumerate the countably
many zeros — no operator content).  Now the pairing is **positive-definite** (`0 < pairing i i`,
strict) so the zero-pairing witness dies, and an actual **operator** `T` self-adjoint w.r.t.
the pairing (`pairing i i * T i j = pairing j j * T j i`) with the spectrum on its diagonal is
required, so a bare spectrum-enumeration no longer witnesses.  This is the SCHEMA of
Hilbert–Pólya only: the analytic content — genuine self-adjointness on a Hilbert space and
the trace identification that would make it RH-equivalent — is the C₅ distance,
manuscript-resident (trail O.18), **DISCLAIMED as ever**.  (A diagonal multiplication operator
still witnesses the schema; that is expected — the schema is not the theorem.)

**C₅-distance marker (W-6-EXT, 2026-07-19):** the certified R5-*input* spectrum `{n²}` provably
does NOT satisfy this face's realization clause — see `certifiedInput_not_zeroRealizing` below,
the compiled fifth-register boundary marker (real-part form; the deeper ordinate form is residue
C5-DIST-A). -/
def Register5_output_HilbertPolya : Prop :=
  ∃ (spectrum : ℕ → ℝ) (pairing : ℕ → ℕ → ℝ) (T : ℕ → ℕ → ℝ),
    (∀ i j, pairing i j = pairing j i) ∧
    (∀ i, 0 < pairing i i) ∧
    (∀ i j, pairing i i * T i j = pairing j j * T j i) ∧
    (∀ n, T n n = spectrum n) ∧
    (∀ σ : ℝ, is_xi_zero σ → ∃ n : ℕ, spectrum n = σ)

/-! ## The edges — P2 discharges

Three graded lists (concordance-first): DERIVES (native, or cross-kernel-at-pin carried by
an attributed named premise), INTERFACES (named classical premise, ξ-pattern), and the
NOT-COMPILED list (documented in the header, never a `sorry`). -/

/-! ### DERIVES edges -/

/-- **DERIVES (native) — goal ⇐ h1 ∧ h2.**  Via `T3.T3prime_shared_witness`: the shared
witness `Phi` turns `(∀ C ∈ 𝒞, C Phi)` and `mellin Phi (s/2) ≠ 0` into the goal state. -/
theorem goalState_of_h1_h2 (𝒞 : Set T3.Coupling) (s : ℂ)
    (h1 : ∀ C ∈ 𝒞, C Phi) (h2 : mellin Phi (s / 2) ≠ 0) :
    GoalState 𝒞 s :=
  T3.T3prime_shared_witness 𝒞 s h1 h2

/-- **DERIVES (native) — the seven-class goal reduces to the open h2.**  `h1` is supplied by
`h1_complete_at_Phi` (projected onto `sevenClasses` membership); only `h2`
(`mellin Phi (s/2) ≠ 0`) remains open. -/
theorem goalState_sevenClasses_of_h2 (s : ℂ) (h2 : mellin Phi (s / 2) ≠ 0) :
    GoalState sevenClasses s := by
  refine goalState_of_h1_h2 sevenClasses s ?_ h2
  obtain ⟨hC1, hC2, hC3, hC4, hC5, hC6, _hC7e, hC7o⟩ := h1_complete_at_Phi
  intro C hC
  simp only [sevenClasses, Set.mem_insert_iff, Set.mem_singleton_iff] at hC
  rcases hC with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hC1
  · exact hC2
  · exact hC3
  · exact hC4
  · exact hC5
  · exact hC6
  · exact hC7o

/-- **DERIVES (native) — R5-input certified at Φ.**  `Register5_input = C5_input`, discharged
by `C5_input_at_Phi`. -/
theorem R5_input_at_Phi : Register5_input Phi :=
  C5_input_at_Phi

/-- **DERIVES (cross-kernel, at SIDE-kernel v1.3 = 0bc21c0) — R2 → RiemannHypothesis.**
`Register2_conservationHypothesis` is the verbatim restatement of
`ConservationBridge.ConservationHypothesis`; the compiled implication to Mathlib's
`RiemannHypothesis` is `ConservationBridge.riemann_hypothesis` at that pin.  The federation
rule bars a Lake dep, so the compiled bridge is carried as an explicit, attributed premise
(definitional identity eye-verifiable at both pins). -/
theorem R2_conservationHypothesis_to_RH
    (kernelBridge : Register2_conservationHypothesis → RiemannHypothesis)
    (h : Register2_conservationHypothesis) : RiemannHypothesis :=
  kernelBridge h

/-- **DERIVES (cross-kernel, at SIDE-li-map = 73cee42) — R4 channel decomposition
λ_n = λ_A(n) + λ_Z(n).**  The Li map is additive over the coefficient stream; compiled
COMBINATORIALLY as `LiLinearMap.lam_add` (stream-level, `η : ℕ → ℤ`).  Carried here as the
attributed additivity premise, instantiated at the archimedean/zero channel split
`(lam_A, lam_Z)`.  **Grade note:** combinatorial stream-level only — the analytic
identification of the stream with the Taylor coefficients of `log ξ` is manuscript-resident
(the two-leg split). -/
theorem R4_channelDecomposition
    {lam : (ℕ → ℤ) → ℕ → ℤ}
    (lam_additive : ∀ (η η' : ℕ → ℤ) (n : ℕ),
      lam (fun j => η j + η' j) n = lam η n + lam η' n)
    (lam_A lam_Z : ℕ → ℤ) (n : ℕ) :
    lam (fun j => lam_A j + lam_Z j) n = lam lam_A n + lam lam_Z n :=
  lam_additive lam_A lam_Z n

/-! ### INTERFACES edges (named premise explicit, ξ-pattern — never a sorry) -/

/-- **INTERFACES — R4 positivity → RiemannHypothesis** via **Li's criterion** (named premise:
Bombieri–Lagarias 1999, `λ_n ≥ 0 ⟺ RH` via the Guinand–Weil explicit formula; **not in
Mathlib**).  The classical bridge is the explicit hypothesis argument. -/
theorem R4_positivity_to_RH
    {lam : ℕ → ℝ}
    (liCriterion : Register4_positivity lam → RiemannHypothesis)
    (h : Register4_positivity lam) : RiemannHypothesis :=
  liCriterion h

/-- **INTERFACES — R1 universality → goal** via the universality bridge (named premise: the
Universal Silence Theorem instantiated at ξ's interfaces). -/
theorem R1_universality_to_goal
    {𝒞 : Set T3.Coupling} {s : ℂ}
    (universalityBridge : Register1_universalityHypothesis → GoalState 𝒞 s)
    (h : Register1_universalityHypothesis) : GoalState 𝒞 s :=
  universalityBridge h

/-- **INTERFACES — R5-output → RiemannHypothesis**, **DISCLAIMED**.  Named premise: the
Hilbert–Pólya realization bridge.  This programme asserts NEITHER `Register5_output_HilbertPolya`
NOR this bridge; the edge is stated only so the disclaimed register's shape is on the record.
Closes over 𝔽_q (Weil 1948), open over ℚ — cited, never claimed. -/
theorem R5_output_HilbertPolya_to_RH
    (hpBridge : Register5_output_HilbertPolya → RiemannHypothesis)
    (h : Register5_output_HilbertPolya) : RiemannHypothesis :=
  hpBridge h

/-! ### The C₅-distance compiled marker (W-6-EXT h2 candidate #4, 2026-07-19)

The fifth register's boundary, made compiled: the CERTIFIED R5-input spectrum `{n²}` provably
CANNOT witness the (disclaimed) R5-output realization face. -/

/-- The certified R5-input spectrum `μ n = n²` (`CouplingsAtPhi.C5_input`, discharged at
`C5_input_at_Phi` via Mathlib's `hasSum_int_evenKernel`), presented as the ℕ-indexed real
spectrum the R5-output realization clause ranges over. -/
def certifiedInputSpectrum : ℕ → ℝ := fun n => (n : ℝ) ^ 2

/-- The R5-output realization clause, extracted **verbatim** from the last conjunct of
`Register5_output_HilbertPolya` (`:190`, spectrum abstracted): a spectrum is *zero-realizing*
iff every nontrivial-ζ-zero real part occurs as a spectrum value.  Definitional identity with
the compiled face — eye-verifiable against `:190`. -/
def RealizesXiZeros (spectrum : ℕ → ℝ) : Prop :=
  ∀ σ : ℝ, is_xi_zero σ → ∃ n : ℕ, spectrum n = σ

/-- **Named classical premise** — a nontrivial ζ-zero exists with real part strictly inside
the critical strip.  Classical status: Riemann's own computed zeros; Hardy (1914) proved
infinitely many lie ON the line; the strip bound `0 < Re < 1` is the classical zero-free-region
consequence.  **Absent from Mathlib at pin `5e932f97`** (the pin carries `RiemannHypothesis`,
the trivial zeros `riemannZeta_neg_two_mul_nat_add_one`, and `riemannZeta 0 = -1/2`, but no
nontrivial-zero existence).  Hence carried as an explicit premise (ξ-pattern). -/
def NontrivialZeroExistsInStrip : Prop :=
  ∃ σ : ℝ, is_xi_zero σ ∧ 0 < σ ∧ σ < 1

/-- **h2 candidate #4 — THE C₅-DISTANCE COMPILED NEGATIVE (INTERFACES).**

The certified R5-input spectrum `{n²}` is **not** a zero-realizing spectrum: it fails the
realization clause of `Register5_output_HilbertPolya`, so no witness of that (disclaimed)
output face can have `spectrum = certifiedInputSpectrum`.

**(a) What it locates.**  The certified R5-*input* spectrum and any spectrum satisfying the
R5-*output* realization clause are provably distinct objects — the fifth register's boundary
marker, the C₅ distance made compiled.  Kin to `C7FiniteTypeFalse.C7_finite_type_false` and
the T7 metric-realization boundary: a negative that names a distance precisely without
shortening it.

**(b) Two-clause disclosure.**  This is the REAL-PART form (`spectrum n = σ`, the pentagon's
`:190` clause).  The deeper distance is the ORDINATE form — `CouplingsAtPhi.C5_output`'s clause
`ρ.im² = μ n`, i.e. `{n²}` vs the squared-ordinate spectrum `{γ²}` — which is UNREACHABLE at
this pin (it needs either a certified zero value or the zero-counting `N(T)`, both absent from
Mathlib `5e932f97`).  Filed as dated residue **C5-DIST-A** (OPEN_TRAILS); reopens when Mathlib
gains either ingredient, or by author ruling.

**(c) What it does NOT claim.**  Nothing about whether some *other* spectrum or operator
realizes the zeros.  Hilbert–Pólya stays **disclaimed** (`Register5_output_HilbertPolya`).
The negative is about *this specific certified spectrum only*.

**(d) On the elementary arithmetic.**  The proof is elementary (real parts lie in `(0,1)`; no
perfect square lies there) precisely BECAUSE the compiled face localizes the distance that
sharply — the depth is not lost, it is relocated into the named residue C5-DIST-A and the
disclaimed premise `NontrivialZeroExistsInStrip`. -/
theorem certifiedInput_not_zeroRealizing
    (nontrivialZeroInStrip : NontrivialZeroExistsInStrip) :
    ¬ RealizesXiZeros certifiedInputSpectrum := by
  intro hReal
  obtain ⟨σ, hz, h0, h1⟩ := nontrivialZeroInStrip
  obtain ⟨n, hn⟩ := hReal σ hz
  have hval : (n : ℝ) ^ 2 = σ := by simpa [certifiedInputSpectrum] using hn
  have hn0 : n ≠ 0 := by
    rintro rfl
    have hσ0 : σ = 0 := by simpa using hval.symm
    linarith
  have h1n : (1 : ℝ) ≤ (n : ℝ) := by
    have : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
    exact_mod_cast this
  have hge1 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith [h1n]
  rw [hval] at hge1
  linarith

end RegisterPentagon
end SIDELvConservation
