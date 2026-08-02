import SIDELvConservation.ZeroActingPairing

/-!
# QWantedPoster — the forced-property constraint set, compiled, with a discriminating screen

BUILD-1 of the h2 build slate (2026-08-01). **Warrant:** the residue analysis characterized the
unbuilt center-object Q from its constraint set — "a wanted poster" (THE_RESIDUE_OF_RH v1.1 §6):
the constraint set pins every property EXCEPT the positive polarization, which is precisely the
disclaimed clause. This module compiles that constraint set as a finite PROFILE layer over the
typed specification `ZeroActingPairing` (this repo, held branch), and arms a conformance SCREEN
that earns its grade by DISCRIMINATING: the two proved suppliers PASS, a known-wrong candidate
FAILS on exactly the clause the compiled negative `certifiedInput_not_zeroRealizing` certifies.

**ANTI-OVERCLAIM (load-bearing).** The profiles are MODEL-LEVEL Boolean summaries. The two PASS
rows record the SHAPES of proved instances (Weil's intersection-form route; the Lee–Yang
ferromagnetic route) as literature-anchored assignments — they re-prove nothing. The FAIL row's
`false` is warranted by the in-repo compiled negative under its named premise. Passing the screen
does NOT construct a Q for ζ; the screen classifies candidate profiles, and the existence of a
conforming instance over ℚ remains exactly the disclaimed clause (`Register5_output_HilbertPolya`,
DISCLAIMED; pentagon precedent: STRUCTURE compiled, never the equivalence).

**Sources per field (rail/monograph at pin; papers cited by version):**
- THE_RESIDUE_OF_RH v1.1 §6 (the 𝔽_q anatomy; `transfer_obstruction_is_the_two_geometric_clauses`;
  the wanted-poster list; "positivity is free — the obstruction is realization").
- monograph A_Place_to_Stand §27.3 register 5 (the fifth register; Weil's route via the
  intersection pairing on correspondences).
- THE_UNCONDITIONAL_SURROUND v0.4 §6/§6a (the node `covers_all`; the positivity register face).
- Face-D control (relay reports/2026-07-29-face-D-function-field.md): the intersection form on
  C×C as the proved supplier over 𝔽_q.
- Lee–Yang control (relay reports/2026-07-31-lee-yang-control.md): the ferromagnetic pair
  coupling as the proved supplier in the circle theorem; the index-arity sort.
- `certifiedInput_not_zeroRealizing` (this repo, RegisterPentagon): the compiled negative that
  warrants the FAIL row.

SECTION 0 — THE SCREEN'S FIRST THEOREM OF USE (filed 2026-08-02, from the maiden run).
The screen mechanically separates CARRIER candidates (objects that would BE the pairing:
Connes-Consani, de Branges, Sonin/CCM — each passes the FE clauses and fails-or-leaves-open
exactly the polarization, in its own vocabulary) from CRITERION routes (tests that would DETECT
the pairing's consequence: the Li route fails the carrier clause itself — a single-index
diagonal, not an object). Screen v2 (the register-lattice weakening): realizesTargetSpectrum
may weaken to diagonal-realization on the Bombieri-Lagarias family — every v1 verdict survives;
a criterion still supplies no carrier. The taxonomy is the instrument's own first finding.

BUILD-4 rides this pass: the Δn₄ row (three-arm probe Arm 1; Face-E two-witness rider (b)) —
the count DERIVES; the cohomological reading carried as a named-premise slot, INTERFACES.

0 sorry, 0 native_decide. HELD on the held branch; nothing deposits.
-/

namespace SIDELvConservation
namespace QWantedPoster

/-- The wanted-poster constraint set, enumerated. Each constraint is one clause of the
characterization THE_RESIDUE_OF_RH v1.1 §6 assembled; the enumeration is the compiled
form of "the constraint set pins every property except the positive polarization." -/
inductive QConstraint where
  /-- pair-index carrier: the object is a PAIRING (acts on pairs; index-arity 2) — the
  index-arity coordinate of the keystone; both proved suppliers are pair-index. -/
  | pairIndexed
  /-- the definiteness clause: positive on the FE-even class (the Poincaré-duality
  polarization over 𝔽_q; the ferromagnetic one-sign structure in Lee–Yang) — THE UNPINNED
  CLAUSE over ℚ (residue §6: pinned everywhere except here). -/
  | positiveOnFEEven
  /-- realization: the spectrum/zero-set is the TARGET one (Frobenius eigenvalues over 𝔽_q;
  the confined zeros in Lee–Yang; the ξ-ordinates for ζ) — the clause the certified input
  provably fails (`certifiedInput_not_zeroRealizing`). -/
  | realizesTargetSpectrum
  /-- the ledger trace: the object consumes a non-negative counting ledger (point counts
  over 𝔽_q; positive coefficients in Lee–Yang; `Λ(n) ≥ 0` for ζ) — the Euler-consuming
  clause of `ZeroActingPairing`. -/
  | carriesLedgerTrace
  /-- distinctness: not the certified `{n²}` input in disguise — the typing clause
  `distinctFromInput` of `ZeroActingPairing`. -/
  | distinctFromCertifiedInput
  deriving DecidableEq

/-- A candidate's profile: the finite Boolean summary of which wanted-poster constraints the
candidate's setting supplies. MODEL-LEVEL (see module header). -/
structure CandidateProfile where
  pairIndexed : Bool
  positiveOnFEEven : Bool
  realizesTargetSpectrum : Bool
  carriesLedgerTrace : Bool
  distinctFromCertifiedInput : Bool
  deriving DecidableEq, Repr

/-- The conformance screen: a profile conforms when every wanted-poster clause is supplied. -/
def screen (p : CandidateProfile) : Bool :=
  p.pairIndexed && p.positiveOnFEEven && p.realizesTargetSpectrum &&
    p.carriesLedgerTrace && p.distinctFromCertifiedInput

/-- **Supplier 1 — the intersection form over 𝔽_q** (Weil 1948; Face-D control). Pair-index
(intersection form on correspondences on C×C); positive on the FE-even class (Hodge index /
Castelnuovo, the Poincaré-duality polarization); realizes the target spectrum (Frobenius
eigenvalues, |α| = √q forced); carries the ledger trace (point counts); distinct from the
certified input. Literature-anchored model assignment of the PROVED instance's shape. -/
def intersectionFormProfile : CandidateProfile :=
  { pairIndexed := true, positiveOnFEEven := true, realizesTargetSpectrum := true,
    carriesLedgerTrace := true, distinctFromCertifiedInput := true }

/-- **Supplier 2 — the ferromagnetic pair coupling** (Lee–Yang 1952; the Lee–Yang control).
Pair-index (couplings J_ij over pairs; Asano pair-gluing); positive one-sign structure
(ferromagnetism, |A| ≤ 1 at the two-spin base); realizes the target spectrum (the confined
zeros on the circle — setting-relative target); carries the ledger trace (positive
coefficients / positive spin measure); distinct from the certified input. Literature-anchored
model assignment of the PROVED instance's shape. -/
def lyCouplingProfile : CandidateProfile :=
  { pairIndexed := true, positiveOnFEEven := true, realizesTargetSpectrum := true,
    carriesLedgerTrace := true, distinctFromCertifiedInput := true }

/-- **The known-wrong candidate — the certified `{n²}` input spectrum.** Positive-definite and
self-adjoint (positivity is free — residue §6), single-index diagonal read as a degenerate
pairing, ledger fine — but `realizesTargetSpectrum := false`, warranted by the compiled negative
`certifiedInput_not_zeroRealizing` (this repo; under its named classical premise, a nontrivial
zero in the open strip); and `distinctFromCertifiedInput := false` by definition (it IS the
certified input). The screen must FAIL it. -/
def certifiedInputProfile : CandidateProfile :=
  { pairIndexed := false, positiveOnFEEven := true, realizesTargetSpectrum := false,
    carriesLedgerTrace := true, distinctFromCertifiedInput := false }

/-- The screen PASSES the intersection-form supplier. -/
theorem screen_passes_intersectionForm : screen intersectionFormProfile = true := rfl

/-- The screen PASSES the Lee–Yang coupling supplier. -/
theorem screen_passes_lyCoupling : screen lyCouplingProfile = true := rfl

/-- The screen FAILS the certified-input candidate. -/
theorem screen_fails_certifiedInput : screen certifiedInputProfile = false := rfl

/-- **THE SCREEN DISCRIMINATES** — it passes both proved suppliers and fails the known-wrong
candidate. This is the validation clause of BUILD-1: the screen earns its grade by
discrimination, not by construction. -/
theorem screen_discriminates :
    screen intersectionFormProfile = true ∧ screen lyCouplingProfile = true ∧
      screen certifiedInputProfile = false :=
  ⟨rfl, rfl, rfl⟩

/-- The certified input fails the screen ON the realization and distinctness clauses while
sharing the positivity and ledger clauses — the compiled profile form of "positivity is free;
the obstruction is realization" (residue §6). -/
theorem certifiedInput_fails_on_realization :
    certifiedInputProfile.positiveOnFEEven = true ∧
      certifiedInputProfile.carriesLedgerTrace = true ∧
      certifiedInputProfile.realizesTargetSpectrum = false := by
  decide

/-! ## BUILD-4 — the Δn₄ row (rides this pass)

Three-arm probe Arm 1 (relay reports/2026-07-29-three-arm-probe.md): the formation tuple over
𝔽_q is (2,3,2,1), over ℚ it is (2,3,2,0); the difference is the ONE bright essential interface
the function field gains — Δn₄ = +1, a certified κ-difference. Face-E two-witness rider (b):
that missing interface IS the codomain of the cup-product pairing H¹×H¹→H² which Spec ℤ lacks.
The COUNT derives; the cohomological READING is carried as a named-premise slot — INTERFACES,
never forced (the identification is a graded reading across vocabularies). -/

/-- The 𝔽_q formation tuple (n₁, n₂, n₃, n₄) = (2, 3, 2, 1). -/
def formationTuple_Fq : ℕ × ℕ × ℕ × ℕ := (2, 3, 2, 1)

/-- The ℚ formation tuple (n₁, n₂, n₃, n₄) = (2, 3, 2, 0). -/
def formationTuple_Q : ℕ × ℕ × ℕ × ℕ := (2, 3, 2, 0)

/-- **DERIVES — the count.** The interface-count difference is exactly one:
Δn₄ = n₄(𝔽_q) − n₄(ℚ) = 1, and the first three coordinates agree. -/
theorem delta_n4_count :
    formationTuple_Fq.2.2.2 = formationTuple_Q.2.2.2 + 1 ∧
      formationTuple_Fq.1 = formationTuple_Q.1 ∧
      formationTuple_Fq.2.1 = formationTuple_Q.2.1 ∧
      formationTuple_Fq.2.2.1 = formationTuple_Q.2.2.1 := by
  decide

/-- **INTERFACES — the Δn₄ row.** The graded row: the count (DERIVES, above) together with the
cohomological reading carried as a named-premise SLOT — `h2Reading` holds the proposition "the
missing n₄ interface is the codomain of the cup-product pairing over ℚ" as a field, never
asserted. Instantiating this structure requires SUPPLYING the reading; the row's grade is
INTERFACES, the identification never forced. -/
structure DeltaN4Row where
  /-- the certified count: Δn₄ = +1 (dischargeable by `delta_n4_count`). -/
  countDerives : formationTuple_Fq.2.2.2 = formationTuple_Q.2.2.2 + 1
  /-- the named-premise slot: the cohomological reading (absent H² codomain), carried openly. -/
  h2Reading : Prop

/-- The count clause of the row is dischargeable now (no premise): the row awaits only its
reading. -/
def deltaN4Row_of_reading (reading : Prop) : DeltaN4Row :=
  { countDerives := (delta_n4_count).1, h2Reading := reading }

end QWantedPoster
end SIDELvConservation
