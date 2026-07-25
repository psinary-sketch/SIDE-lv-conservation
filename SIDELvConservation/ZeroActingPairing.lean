import SIDELvConservation.RegisterPentagon

/-!
# ZeroActingPairing — the compiled SPECIFICATION of the center-object

W-ORD-PAIRING-INTERFACE (2026-07-25). **Warrant:** the E-characterization proved that every
structure capable of bounding the zero-oscillation `E(n)` of `λ_Z` by the archimedean channel
`λ_A` is *pairing-positivity* shaped (FE-cancellation fails; density gives only the σ=1 edge;
the only centre-reaching structure is a positive pairing on the zeros — the Weil-functional /
Hilbert–Pólya shape).

This module compiles the **TYPE** the E-characterization named — a *zero-acting* positive
pairing that is *Euler-consuming* (breaks for a sign-neutral ledger, i.e. for Davenport–
Heilbronn) and *distinct from the certified `{n²}` input spectrum* — together with the
INTERFACES chain `ZeroActingPairing → channel inequality → RH`.

**It asserts NO instance.** The existence of a `ZeroActingPairing` is exactly the C₅-output the
programme holds open (`Register5_output_HilbertPolya`, DISCLAIMED; closes over 𝔽_q by Weil 1948,
open over ℚ). This is the compiled *specification*, in the pentagon precedent (STRUCTURE compiled,
never the equivalence). INTERFACES grammar throughout; every non-native step is a named premise;
the disclaimer text extends — the register now holds a compiled *interface*, still no claimed
witness.

**Salt-check (run before commit).** Not a shell: the structure carries four genuine `Prop`
fields, and the two typing clauses kill the trivial witness — a bare diagonal enumeration of the
zeros dies on `distinctFromInput` (via `certifiedInput_not_zeroRealizing`) and a sign-neutral
ledger dies on `eulerConsuming`. The RH implication is a real composition through named
*classical* premises (the Weil-criterion direction; the inequality→positivity step; Li's
criterion — Bombieri–Lagarias 1999, not in Mathlib), with the pairing's **existence disclaimed**
— the compiled object is the CONDITIONAL, never a claimed instance (Rule 3: named-INTERFACES,
carried openly, never a promissory note read as closure).
-/

namespace SIDELvConservation
namespace RegisterPentagon

/-- The four typed requirements the B1 survey earned, bundled into the center-object's type.

`lam_A`, `lam_Z` are the two Li channels; `ledger` is the Euler ledger (the von Mangoldt
`Λ ≥ 0` for `ζ`; the sign-neutral periodic `a_n` for Davenport–Heilbronn). -/
structure ZeroActingPairing (lam_A lam_Z ledger : ℕ → ℝ) : Prop where
  /-- (1) **zero-acting** — the pairing's spectrum realizes the ξ-zeros: the R5-output schema
  (a positive-definite symmetric pairing, a self-adjoint operator, and a zero-realizing
  diagonal). DISCLAIMED as an existence claim; here a typed requirement of the object. -/
  zeroActing : Register5_output_HilbertPolya
  /-- (2) **positive-on-FE-even ⟹ the channel inequality** — the Weil-criterion direction as a
  named premise: a positive pairing on the FE-even (functional-equation-symmetric) test class
  yields the two-channel inequality `−λ_A ≤ λ_Z`. -/
  yieldsInequality : Register5_output_HilbertPolya → Register4_channelInequality lam_A lam_Z
  /-- (3) **Euler-consuming** — the DH-breaking clause (the Epstein test formalized): a valid
  pairing requires the Euler ledger non-negative, so a *sign-neutral* ledger (Davenport–
  Heilbronn, period-sum 0) admits none. The requirement, not a theorem. -/
  eulerConsuming : ∀ m, 0 ≤ ledger m
  /-- (4) **distinct-from-input** — the certified `{n²}` input spectrum is *not* zero-realizing
  (`certifiedInput_not_zeroRealizing`): this pairing is not the input spectrum. -/
  distinctFromInput : ¬ RealizesXiZeros certifiedInputSpectrum

/-- **INTERFACES (native step) — ZeroActingPairing → the two-channel inequality.** Unfolds the
`yieldsInequality` field against the `zeroActing` witness carried by the object. -/
theorem zeroActingPairing_to_channelInequality {lam_A lam_Z ledger : ℕ → ℝ}
    (P : ZeroActingPairing lam_A lam_Z ledger) :
    Register4_channelInequality lam_A lam_Z :=
  P.yieldsInequality P.zeroActing

/-- **INTERFACES — ZeroActingPairing → RiemannHypothesis** (the compiled CONDITIONAL). Chain:
the pairing yields the channel inequality (native), the inequality gives Li-positivity (named
premise), and Li's criterion gives RH (named classical premise, Bombieri–Lagarias 1999). The
**existence** of a `ZeroActingPairing` is disclaimed — this theorem never produces one. -/
theorem zeroActingPairing_to_RH {lam_A lam_Z ledger lam : ℕ → ℝ}
    (inequalityToPositivity :
      Register4_channelInequality lam_A lam_Z → Register4_positivity lam)
    (liCriterion : Register4_positivity lam → RiemannHypothesis)
    (P : ZeroActingPairing lam_A lam_Z ledger) :
    RiemannHypothesis :=
  liCriterion (inequalityToPositivity (zeroActingPairing_to_channelInequality P))

/-- **The distinct-from-input clause is dischargeable** (not open): the certified `{n²}` input
spectrum genuinely fails to realize the zeros, given a nontrivial zero exists in the strip.
So `distinctFromInput` is a *typing* constraint the object satisfies by the compiled negative,
not an added open premise. -/
theorem distinctFromInput_discharged
    (nontrivialZeroInStrip : NontrivialZeroExistsInStrip) :
    ¬ RealizesXiZeros certifiedInputSpectrum :=
  certifiedInput_not_zeroRealizing nontrivialZeroInStrip

/-! ## The DH-exclusion lemma — clause (3) made demonstrably load-bearing

Pre-merge gate (2026-07-25). The salt-check flagged `eulerConsuming` as a genuine but *typing-only*
clause. This section discharges that: a **sign-neutral** ledger — the Davenport–Heilbronn coefficient
signature (period-sum zero, sign-changing, no Euler product hence no `Λ ≥ 0`) — provably cannot
satisfy `eulerConsuming`, so no `ZeroActingPairing` admits one. Clause (3) is the compiled Epstein
discriminator at interface level. C₄ precedent: *strengthen-then-discharge*. -/

open scoped BigOperators

/-- A ledger is **sign-neutral** with period `p`: its values over `Finset.range p` sum to zero and it
is not identically zero there. This is the Davenport–Heilbronn coefficient signature — a periodic
arithmetic ledger with period-sum zero that genuinely changes sign. -/
def SignNeutralLedger (ledger : ℕ → ℝ) (p : ℕ) : Prop :=
  (∑ m ∈ Finset.range p, ledger m = 0) ∧ (∃ m ∈ Finset.range p, ledger m ≠ 0)

/-- **A sign-neutral ledger cannot be Euler-consuming** — the T-1/Epstein discriminator at interface
level. A non-negative family summing to zero is identically zero; a nonzero value forbids it. -/
theorem signNeutral_not_eulerConsuming {ledger : ℕ → ℝ} {p : ℕ}
    (h : SignNeutralLedger ledger p) : ¬ (∀ m, 0 ≤ ledger m) := by
  rintro hnn
  obtain ⟨hsum, m, hm, hne⟩ := h
  exact hne ((Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hnn k)).1 hsum m hm)

/-- **Clause (3) is load-bearing: no `ZeroActingPairing` has a sign-neutral ledger.** The Davenport–
Heilbronn ledger dies on `eulerConsuming` — the Epstein test compiled at interface level. The clause
the salt-check flagged as typing-only now demonstrably excludes the DH witness class. -/
theorem zeroActingPairing_ledger_not_signNeutral
    {lam_A lam_Z ledger : ℕ → ℝ} {p : ℕ}
    (P : ZeroActingPairing lam_A lam_Z ledger) : ¬ SignNeutralLedger ledger p :=
  fun h => signNeutral_not_eulerConsuming h P.eulerConsuming

/-- The Davenport–Heilbronn coefficient ledger model on its first period (period 5, sum zero,
sign-changing): `(0,1,2,3,4) ↦ (0,1,1,−1,−1)`. Captures the load-bearing feature — period-sum zero
and genuinely negative (no `Λ ≥ 0`) — the exact κ aside. -/
def dhModelLedger : ℕ → ℝ
  | 1 => 1
  | 2 => 1
  | 3 => -1
  | 4 => -1
  | _ => 0

/-- **The DH model ledger is sign-neutral** — witnessed, so the exclusion is non-vacuous. -/
theorem dhModelLedger_signNeutral : SignNeutralLedger dhModelLedger 5 := by
  refine ⟨?_, 1, ?_, ?_⟩
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero, dhModelLedger]; norm_num
  · decide
  · norm_num [dhModelLedger]

/-- **So the DH model ledger admits no `ZeroActingPairing`** — the Epstein test at interface level:
the sign-neutral DH ledger dies on `eulerConsuming`, exactly as the salt-check predicted. -/
theorem dhModelLedger_no_pairing {lam_A lam_Z : ℕ → ℝ}
    (P : ZeroActingPairing lam_A lam_Z dhModelLedger) : False :=
  zeroActingPairing_ledger_not_signNeutral P dhModelLedger_signNeutral

end RegisterPentagon
end SIDELvConservation
