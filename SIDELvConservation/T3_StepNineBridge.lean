import Mathlib.Analysis.MellinTransform
import Mathlib.NumberTheory.LSeries.Dirichlet
import SIDELvConservation.T1_MellinFactorization
import SIDELvConservation.T2_SDarkness

/-!
# T3 — the step-(9) bridge (per-class exclusion ⟹ all-combinations exclusion)

The load-bearing target of the LV-Conservation programme.  Formalization
plan (per work order):

1. Define "coupling contributes only through `Φ`".
2. Prove that the zero set of `s ↦ mellin Φ (s / 2)` is a function of
   `Φ` (T3a) — trivial via T1, elevated to a named theorem.
3. Show that a *joint* witness `Φ` satisfying every coupling and having
   `mellin Φ (s / 2) ≠ 0` at `s` immediately gives combined exclusion
   (T3b) — trivial existential extraction.
4. Attempt the main bridge (T3_main): per-class exclusion at `s`
   ⟹ combined exclusion at `s`.

The manuscript argument is: zero locations are spectral (s-side) data;
inter-class couplings contribute only to `Φ` (s-independent side); hence
combinations of classes cannot produce s-side effects no single class
produces.

At the level of quantifiers this asks
`(∀ C ∈ 𝒞, ∃ Φ, C Φ ∧ mellin Φ (s/2) ≠ 0) → ∃ Φ, (∀ C ∈ 𝒞, C Φ) ∧ …`.
The move from `∀∃` to `∃∀` is not free without a witness-selection or
cofinality assumption on the class family in `Φ`-space.  This is exactly
the **emergent-totality question** flagged in FINDINGS F.2026-07-09-b.
Per work-order T3 rules, we STOP at this step with one pinned `sorry`
and no weakened statement.
-/

namespace SIDELvConservation
namespace T3

open Complex MeasureTheory

/-- A **coupling** is a constraint on the fixed Mellin integrand `Φ`
supplied by T1.  Physical realizations of interest include the product
formula and the distributive law — but the theorem is about the
propositional shape, not the specific coupling. -/
abbrev Coupling := (ℝ → ℂ) → Prop

/-- The zero-location set of `s ↦ mellin Φ (s / 2)`.  Manifestly a
function of `Φ`. -/
def ZeroLoc (Φ : ℝ → ℂ) : Set ℂ := {s | mellin Φ (s / 2) = 0}

/-- Per-class exclusion at `s`: coupling `C` is consistent with a `Φ`
whose Mellin factor has *no* zero at `s`. -/
def PerClassExcludes (C : Coupling) (s : ℂ) : Prop :=
  ∃ Φ : ℝ → ℂ, C Φ ∧ mellin Φ (s / 2) ≠ 0

/-- Combinations exclude at `s`: the joint constraint over a family of
couplings is consistent with a `Φ` whose Mellin factor has no zero at `s`. -/
def CombinationsExclude (𝒞 : Set Coupling) (s : ℂ) : Prop :=
  ∃ Φ : ℝ → ℂ, (∀ C ∈ 𝒞, C Φ) ∧ mellin Φ (s / 2) ≠ 0

/-- **T3a.**  The zero-location set is a function of `Φ`.  Restatement of
Mathlib's `mellin` definition: `Φ` is the sole input to
`s ↦ mellin Φ (s / 2)`; therefore its zero-set is determined by `Φ`. -/
theorem T3a_zeroLoc_is_function_of_Phi
    (Φ₁ Φ₂ : ℝ → ℂ) (h : Φ₁ = Φ₂) :
    ZeroLoc Φ₁ = ZeroLoc Φ₂ := by
  subst h; rfl

/-- **T3b.**  If a single `Φ` satisfies every coupling in `𝒞` and has no
zero at `s`, then combined exclusion at `s` holds.  Trivial existential
extraction — the substantive content is *finding* such a `Φ`. -/
theorem T3b_joint_witness_gives_combinations_exclude
    (𝒞 : Set Coupling) (s : ℂ) (Φ : ℝ → ℂ)
    (hJoint : ∀ C ∈ 𝒞, C Φ) (hNonzero : mellin Φ (s / 2) ≠ 0) :
    CombinationsExclude 𝒞 s :=
  ⟨Φ, hJoint, hNonzero⟩

/-- **T3 main — step-(9) bridge, stated, not proved; open.**  For a family
`𝒞` and a point `s`: per-class exclusion at `s` ⟹ combined exclusion at `s`,
as a `Prop`.

Formal reading: the hypothesis is
`∀ C ∈ 𝒞, ∃ Φ_C, C Φ_C ∧ mellin Φ_C (s / 2) ≠ 0`,
and the conclusion asks for a *single* `Φ` witnessing every `C ∈ 𝒞`
simultaneously with `mellin Φ (s / 2) ≠ 0` — a `∀∃ ⟹ ∃∀` commutation with
no free witness (FINDINGS F.2026-07-09-b).  Its universal form is refuted in
this file by `T3doubleprime_general_commutation_fails`; it holds under
Determination's shared witness by `T3prime_shared_witness`.  Restated at b648
under the author's ruling (R258)(2) from a `theorem` closed by `sorry`; that
history is in this file's git log. -/
def T3_perClass_to_combinations (𝒞 : Set Coupling) (s : ℂ) : Prop :=
  (∀ C ∈ 𝒞, PerClassExcludes C s) → CombinationsExclude 𝒞 s

/-- **T3′ — the bridge closes under Determination's shared witness.**
If the programme's Determination condition is in force, every coupling
in `𝒞` is satisfied by the *same* `Φ` — namely T1's fixed `Phi` — and
that `Phi` has non-vanishing Mellin factor at `s / 2`.  The `∀∃ ⟹ ∃∀`
gap of T3 collapses trivially: the shared witness `Phi` is both the
existential witness for every per-class formulation and the joint
witness for the combined formulation.

This is not a weakening of T3; the hypotheses `h1, h2` name the extra
information that Determination supplies.  The proof is
`⟨Phi, h1, h2⟩` — no bookkeeping, no swap. -/
theorem T3prime_shared_witness
    (𝒞 : Set Coupling) (s : ℂ)
    (h1 : ∀ C ∈ 𝒞, C Phi)
    (h2 : mellin Phi (s / 2) ≠ 0) :
    ∃ Φ : ℝ → ℂ, (∀ C ∈ 𝒞, C Φ) ∧ mellin Φ (s / 2) ≠ 0 :=
  ⟨Phi, h1, h2⟩

/-- **T3″ — countermodel: the *unrestricted* bridge fails.**  Without
Determination's shared witness, the general `∀∃ ⟹ ∃∀` implication over
`(𝒞, s)` is false.  Witnessed at `s = 3` by two integrands that agree on
`Ioi 0` (so both have the same non-vanishing Mellin factor there, namely
`completedRiemannZeta 3 ≠ 0`) but disagree at `t = -1` (so no `Φ` can
satisfy both `Φ = f₁` and `Φ = f₂` simultaneously).

Consequence: Determination is doing real work in T3′ — the bridge would
be unprovable without it. -/
theorem T3doubleprime_general_commutation_fails :
    ¬ ∀ (𝒞 : Set Coupling) (s : ℂ),
        (∀ C ∈ 𝒞, ∃ Φ : ℝ → ℂ, C Φ ∧ mellin Φ (s / 2) ≠ 0) →
        ∃ Φ : ℝ → ℂ, (∀ C ∈ 𝒞, C Φ) ∧ mellin Φ (s / 2) ≠ 0 := by
  intro habs
  -- Countermodel data.
  let s0 : ℂ := 3
  let f1 : ℝ → ℂ := fun t => if 0 < t then Phi t else (0 : ℂ)
  let f2 : ℝ → ℂ := fun t => if 0 < t then Phi t else (1 : ℂ)
  let C1 : Coupling := fun Φ => Φ = f1
  let C2 : Coupling := fun Φ => Φ = f2
  let 𝒞 : Set Coupling := {C1, C2}
  -- Convergence condition for T2's completedRiemannZeta ↔ mellin identity.
  have hRe : 1 < s0.re := by show (1 : ℝ) < 3; norm_num
  -- Nonvanishing of mellin Phi at s0/2, via completedRiemannZeta 3 ≠ 0.
  have hMelPhi : mellin Phi (s0 / 2) ≠ 0 := by
    rw [← completedRiemannZeta_eq_mellinPhi s0 hRe]
    intro hCZ
    apply riemannZeta_ne_zero_of_one_lt_re hRe
    have hs0ne : s0 ≠ 0 := by
      show (3 : ℂ) ≠ 0; norm_num
    rw [riemannZeta_def_of_ne_zero hs0ne, hCZ, zero_div]
  -- Mellin transforms of f1, f2 coincide with mellin Phi at s0/2:
  -- integrands agree on Ioi 0.
  have hMelF1 : mellin f1 (s0 / 2) = mellin Phi (s0 / 2) := by
    unfold mellin
    refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro t ht
    show (t : ℂ) ^ (s0 / 2 - 1) • f1 t = (t : ℂ) ^ (s0 / 2 - 1) • Phi t
    show (t : ℂ) ^ (s0 / 2 - 1) • (if 0 < t then Phi t else (0 : ℂ))
        = (t : ℂ) ^ (s0 / 2 - 1) • Phi t
    rw [if_pos (Set.mem_Ioi.mp ht)]
  have hMelF2 : mellin f2 (s0 / 2) = mellin Phi (s0 / 2) := by
    unfold mellin
    refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro t ht
    show (t : ℂ) ^ (s0 / 2 - 1) • f2 t = (t : ℂ) ^ (s0 / 2 - 1) • Phi t
    show (t : ℂ) ^ (s0 / 2 - 1) • (if 0 < t then Phi t else (1 : ℂ))
        = (t : ℂ) ^ (s0 / 2 - 1) • Phi t
    rw [if_pos (Set.mem_Ioi.mp ht)]
  -- The hypothesis of the (assumed) commutation.
  have hHyp : ∀ C ∈ 𝒞, ∃ Φ : ℝ → ℂ, C Φ ∧ mellin Φ (s0 / 2) ≠ 0 := by
    intro C hC
    rcases hC with rfl | hC
    · exact ⟨f1, rfl, hMelF1.symm ▸ hMelPhi⟩
    · rcases hC with rfl
      exact ⟨f2, rfl, hMelF2.symm ▸ hMelPhi⟩
  -- Extract the (assumed) joint witness — but it must equal both f1 and f2.
  obtain ⟨Φ, hCall, _⟩ := habs 𝒞 s0 hHyp
  have hΦeqf1 : Φ = f1 :=
    hCall C1 (Set.mem_insert _ _)
  have hΦeqf2 : Φ = f2 :=
    hCall C2 (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hf12 : f1 = f2 := hΦeqf1.symm.trans hΦeqf2
  -- Evaluate at t = -1, outside Ioi 0: f1 (-1) = 0, f2 (-1) = 1, so 0 = 1.
  have hEval := congr_fun hf12 (-1 : ℝ)
  have hNot : ¬ (0 : ℝ) < -1 := by norm_num
  simp only [f1, f2, if_neg hNot] at hEval
  -- hEval : (0 : ℂ) = 1
  exact zero_ne_one hEval

end T3
end SIDELvConservation
