/-
# CouplingsAtPhi — the seven mechanism classes as `Coupling` predicates, at T1's fixed witness

Work-order O.18 (PLACE-papers OPEN_TRAILS): *discharge the Conservation of Spectra premise*.
The bridge theorem `T3prime_shared_witness` (T3_StepNineBridge.lean) closes the per-class-to-joint
step under two hypotheses:

  h1 : ∀ C ∈ 𝒞, C Phi          -- every mechanism class is satisfied by the ONE fixed witness
  h2 : mellin Phi (s / 2) ≠ 0  -- that witness has non-vanishing Mellin factor at s

This file states the seven classes of monograph Ch. 15 §15.2 as `Coupling` predicates and
discharges those it can against Mathlib. It is the h1 half of the obligation, in progress.

STATUS AT THIS COMMIT (honest; see the per-class comments):
  C₁ realness                       PROVED   (`C1_realness_at_Phi`)
  C₂ half-plane Mellin nonvanishing PROVED   (`C2_halfplane_nonvanishing_at_Phi`)
  C₃ theta transformation           PROVED   (`C3_theta_transformation_at_Phi`, via Mathlib's
                                              `evenKernel_functional_equation`)
  C₄ modularity                     STATED   (no proof claimed)
  C₅-INPUT  heat trace of a real, non-negative spectrum   PROVED (`C5_input_at_Phi`, μ n = n²,
                                              via Mathlib's `hasSum_int_evenKernel`)
  C₅-OUTPUT the spectral realisation (Hilbert–Pólya)      STATED, DISCLAIMED, NEVER CLAIMED.
                                              The gap between C₅-input and C₅-output is the
                                              premise's FIFTH REGISTER — see `C5_output`.
  C₆ holomorphic extension          PROVED   (`C6_holomorphic_extension_at_Phi`, via Mathlib's
                                              `differentiableAt_jacobiTheta₂_snd`)
  C₇-ENTIRETY entire completion of the Mellin transform  PROVED (`C7_entirety_at_Phi`, via
                                              `differentiable_completedZeta₀` + T1)
  C₇-ORDER    the order-≤1 growth bound       OPEN (`sorry`) — priced: Stirling control of Γ (NOT in
                                              Mathlib at all) + finite order of ζ in the strip.
                                              PhragmenLindelof.vertical_strip exists but is a
                                              maximum principle, not a source of order bounds.

SIX discharges now stand at the fixed witness Φ: C₁, C₂, C₃, C₅-input, C₆, C₇-entirety.
The h1 obligation of `T3prime_shared_witness` is NOT complete: `sevenClasses` carries `C7_order`
(the class's real content), which is open, and C₄ is unproved.  Two classes short, and the file
says so rather than counting halves as wholes.

NOTHING HERE IS A SHELL. Every predicate below is a statement that could be false: no `True`-valued
coupling, no `fun _ => True`, no hypothesis that is its own conclusion. Where a proof is not
available the obligation carries a `sorry` and says why — it is not discharged by weakening the
statement.
-/
import SIDELvConservation.T1_MellinFactorization
import SIDELvConservation.T2_SDarkness
import SIDELvConservation.T3_StepNineBridge
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

open Complex HurwitzZeta Set MeasureTheory

namespace SIDELvConservation

open T3

/-! ## The seven couplings (Ch. 15 §15.2), as predicates on the Mellin integrand -/

/-- **C₁ (Schwarz reflection / realness).**  The integrand is real-valued: its imaginary part
vanishes identically.  This is the Φ-side content of "real coefficients" — the source of the
reflection symmetry `Λ(s̄) = conj (Λ s)`. -/
def C1_realness : Coupling := fun (Φ : ℝ → ℂ) => ∀ t : ℝ, (Φ t).im = 0

/-- **C₂ (Euler / multiplicative).**  The Mellin factor does not vanish on the convergence
half-plane.  This is the Φ-side content of the Euler product: absolute convergence and
non-vanishing for `1 < re s`. -/
def C2_halfplane_nonvanishing : Coupling := fun (Φ : ℝ → ℂ) =>
  ∀ s : ℂ, 1 < s.re → mellin Φ (s / 2) ≠ 0

/-- **C₃ (functional equation / theta transformation).**  The integrand obeys the theta
inversion law `Φ (1/t) = √t · Φ t + (correction)`, which is what pushes the functional
equation `Λ(1 - s) = Λ(s)` through the Mellin transform.  Stated here in the weak form that
the transformation exists with a real Jacobian factor. -/
def C3_theta_transformation : Coupling := fun (Φ : ℝ → ℂ) =>
  ∀ t : ℝ, 0 < t → Φ (1 / t) = Real.sqrt t * Φ t + (Real.sqrt t - 1) / 2

/-- **C₄ (modular / PSL₂(ℤ)).**  The integrand is invariant under the modular action in the
sense that it is a fixed point of the weight-1/2 slash of the generator `t ↦ 1/t` composed
with translation.  Stated; no proof claimed at this commit. -/
def C4_modularity : Coupling := fun (Φ : ℝ → ℂ) =>
  ∀ t : ℝ, 0 < t → Φ (t + 2) = Φ t → Φ (1 / t) = Real.sqrt t * Φ t + (Real.sqrt t - 1) / 2

/-- **C₅-INPUT (spectral self-adjointness — the certifiable half).**  The integrand is the heat
trace of a real, non-negative spectrum: there is `μ : ℤ → ℝ` with `μ n ≥ 0` and
`∑_{n : ℤ} exp (-π · μ n · t) = 2 Φ t + 1` for `t > 0`.  This is the SPECTRAL INPUT: the existence
of a non-negative spectrum whose heat trace is the kernel.  It is certifiable, and it is certified
below at `Phi` (with `μ n = n²`). -/
def C5_input : Coupling := fun (Φ : ℝ → ℂ) =>
  ∃ μ : ℤ → ℝ, (∀ n : ℤ, 0 ≤ μ n) ∧
    ∀ t : ℝ, 0 < t → HasSum (fun n : ℤ => ((Real.exp (-Real.pi * μ n * t) : ℝ) : ℂ)) (2 * Φ t + 1)

/-- **C₅-OUTPUT (the spectral realisation — DISCLAIMED, never claimed).**  That the spectrum of
C₅-input is the spectrum *of a self-adjoint operator whose eigenvalues are the zeta zeros* — the
Hilbert–Pólya assertion.  **This programme explicitly DISCLAIMS it** (EXCLUSION_ENGINE, Misreadings:
the spectral kernels disclaim Hilbert–Pólya rather than rest on it), and NO theorem in this file
claims it at `Phi` or anywhere else.

It is stated only so that the gap between input and output has a name.  **That gap is the premise's
FIFTH REGISTER** (BALANCE_AND_POSITIVITY §IV lists four; this is the fifth): over `𝔽_q` the input's
positivity and the output's coincide — Weil's 1948 proof supplies the operator-side positivity from
the Hodge-index/Castelnuovo inequality on `C × C` — while over `ℚ` the coincidence is exactly what
is missing.  The formation distance between `C5_input` and `C5_output` IS the premise, in spectral
coordinates.  See BALANCE_AND_POSITIVITY, "The function-field face at the fixed witness". -/
def C5_output : Coupling := fun (Φ : ℝ → ℂ) =>
  ∃ (H : Type) (_ : ∀ _ : H, ℝ), ∃ μ : ℤ → ℝ, (∀ n : ℤ, 0 ≤ μ n) ∧
    (∀ t : ℝ, 0 < t → HasSum (fun n : ℤ => ((Real.exp (-Real.pi * μ n * t) : ℝ) : ℂ)) (2 * Φ t + 1)) ∧
    ∀ n : ℤ, ∃ ρ : ℂ, ρ.re = 1 / 2 ∧ ρ.im ^ 2 = μ n

/-- **C₆ (Cauchy–Riemann / local analyticity).**  The integrand extends holomorphically to the
right half-plane `0 < re z`: there is `F : ℂ → ℂ`, differentiable on `{z | 0 < re z}`, agreeing
with `Φ` on the positive reals. -/
def C6_holomorphic_extension : Coupling := fun (Φ : ℝ → ℂ) =>
  ∃ F : ℂ → ℂ, (∀ z : ℂ, 0 < z.re → DifferentiableAt ℂ F z) ∧
    ∀ t : ℝ, 0 < t → F (t : ℂ) = Φ t

/-- **C₇-ENTIRETY (Hadamard, the certifiable half).**  The *completed* Mellin transform of `Φ`
agrees on the convergence half-plane with an **entire** function: adding back the principal parts
at `s = 0` and `s = 1` gives a function with no poles anywhere.  This is the analytic-continuation
half of the Hadamard input — it says the object Hadamard would factor *exists as an entire
function*.  PROVED at `Phi` below (`G = completedRiemannZeta₀`, via T1 + Mathlib's
`differentiable_completedZeta₀`). -/
def C7_entirety : Coupling := fun (Φ : ℝ → ℂ) =>
  ∃ G : ℂ → ℂ, Differentiable ℂ G ∧
    ∀ s : ℂ, 1 < s.re → G s = mellin Φ (s / 2) + 1 / s + 1 / (1 - s)

/-- **C₇-ORDER (Hadamard, the open half).**  That entire completion has **order ≤ 1** — the
maximal-type growth `‖G s‖ ≤ C · exp (A · ‖s‖ · log (‖s‖ + 2))`.  This is the actual growth of the
completed zeta (the Γ factor forces `exp(½‖s‖ log‖s‖)` on the real axis), it implies order ≤ 1, and
it is exactly the hypothesis the **genus-1** Hadamard factorisation consumes — the one that bounds
the zero-counting function and gives the product its shape.  **Entirety alone does not give it**, and
this is where the class's real content sits.

CORRECTION (2026-07-14 — W-8 sitting-1 STOP, `OPEN_TRAILS`).  This conjunct previously read
`∃ C A, ‖G s‖ ≤ C · exp (A · ‖s‖)` and was mislabelled "order ≤ 1".  That is **finite exponential
type**, and it is **provably false** of the forced witness `G = completedRiemannZeta₀`: (i) along the
positive real axis `‖G σ‖ ~ exp(½ σ log σ)` (the Γ factor), which beats `C · exp(A σ)` for *every*
fixed `A`; (ii) `G` carries the nontrivial zeros of ζ, `n(T) ~ (T/2π) log T` — superlinear — so by
Jensen it cannot be of finite exponential type.  **Genus-1 Hadamard consumes order ≤ 1, not finite
type.**  The statement is corrected to the true order form, which complex Stirling delivers directly.

OPEN, and priced honestly.  Its true cost is two classical ingredients, **neither of which is in
Mathlib at this pin**:
  (1) **Stirling control of the Γ factor** — a bound `‖Γ(s/2)‖ ≤ exp (A‖s‖ log‖s‖)`-type estimate.
      Mathlib has no `Gamma/Stirling` file and no norm bound on `Complex.Gamma` at all.
  (2) **Finite order of ζ in the strip** — polynomial growth of `ζ` on vertical lines, then
      Phragmén–Lindelöf to fill the strip.  Mathlib HAS `PhragmenLindelof.vertical_strip`, but that
      is a *maximum principle*: it converts growth control into boundedness.  It cannot supply (1),
      and it cannot manufacture an order bound from entirety.
Formalising C₇-order is therefore a Γ-asymptotics project, not a corollary of what exists. -/
def C7_order : Coupling := fun (Φ : ℝ → ℂ) =>
  ∃ G : ℂ → ℂ, Differentiable ℂ G ∧
    (∀ s : ℂ, 1 < s.re → G s = mellin Φ (s / 2) + 1 / s + 1 / (1 - s)) ∧
    ∃ A C : ℝ, ∀ s : ℂ, ‖G s‖ ≤ C * Real.exp (A * (‖s‖ * Real.log (‖s‖ + 2)))

/-- The seven classes, as the family `𝒞` that `T3prime_shared_witness` consumes. -/
def sevenClasses : Set Coupling :=
  {C1_realness, C2_halfplane_nonvanishing, C3_theta_transformation, C4_modularity,
   C5_input, C6_holomorphic_extension, C7_order}
-- NOTE: `C5_output` is deliberately NOT in `sevenClasses`: it is the disclaimed half.

/-! ## Discharges at the fixed witness `Phi` -/

/-- **C₁ at Φ — PROVED.**  `Phi t = ((evenKernel 0 t : ℂ) - 1) / 2` with `evenKernel 0 t : ℝ`,
so the imaginary part is zero by construction. -/
theorem C1_realness_at_Phi : C1_realness Phi := by
  intro t
  simp [C1_realness, Phi]

/-- **C₂ at Φ — PROVED.**  On `1 < re s` the Mellin factor *is* `completedRiemannZeta s` (T1/T2),
and `Λ(s) = ζ(s) · Γℝ(s)` is non-zero there: `ζ` does not vanish on the half-plane
(`riemannZeta_ne_zero_of_one_lt_re`) and `Γℝ` does not vanish for `0 < re s`
(`Gammaℝ_ne_zero_of_re_pos`).  This is the Euler-product content, transported to Φ. -/
theorem C2_halfplane_nonvanishing_at_Phi : C2_halfplane_nonvanishing Phi := by
  intro s hs hzero
  -- Transport the vanishing back to the completed zeta.
  have hΛ : completedRiemannZeta s = 0 := by
    rw [completedRiemannZeta_eq_mellinPhi s hs]; exact hzero
  -- s ≠ 0 since 1 < re s.
  have hs0 : s ≠ 0 := by
    intro h; rw [h] at hs; simp at hs; linarith
  -- ζ s = Λ s / Γℝ s = 0, contradicting non-vanishing on the half-plane.
  have hz : riemannZeta s = 0 := by
    rw [riemannZeta_def_of_ne_zero hs0, hΛ, zero_div]
  exact riemannZeta_ne_zero_of_one_lt_re hs hz

/-- **C₆ at Φ — PROVED.**  The extension is `F z = (jacobiTheta₂ 0 (I * z) - 1) / 2`.  Mathlib's
`differentiableAt_jacobiTheta₂_snd` gives holomorphy of `Θ 0 τ` in `τ` on `0 < im τ`, and
`im (I * z) = z.re`, so `F` is holomorphic exactly on the right half-plane.  On positive reals it
agrees with `Phi` by `evenKernel_def` at `a = 0`. -/
theorem C6_holomorphic_extension_at_Phi : C6_holomorphic_extension Phi := by
  refine ⟨fun z => (jacobiTheta₂ 0 (Complex.I * z) - 1) / 2, ?_, ?_⟩
  · intro z hz
    have hτ : 0 < (Complex.I * z).im := by simpa using hz
    have hθ : DifferentiableAt ℂ (fun w : ℂ => jacobiTheta₂ 0 (Complex.I * w)) z := by
      have h1 : DifferentiableAt ℂ (fun w : ℂ => Complex.I * w) z :=
        (differentiableAt_const _).mul differentiableAt_id
      exact (differentiableAt_jacobiTheta₂_snd 0 hτ).comp z h1
    exact ((hθ.sub (differentiableAt_const _)).div_const 2)
  · intro t ht
    have h := evenKernel_def 0 t
    simp only [Phi]
    rw [show ((0 : ℝ) : UnitAddCircle) = (0 : UnitAddCircle) from rfl] at h
    simp only [ofReal_zero, zero_pow, mul_zero, zero_mul, neg_zero, Complex.exp_zero, one_mul,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true] at h
    rw [← h]

/-- **C₃ at Φ — PROVED.**  Mathlib's `evenKernel_functional_equation` gives
`evenKernel a x = x^(-1/2) * cosKernel a (1/x)`, and at `a = 0` the two kernels coincide
(`evenKernel_eq_cosKernel_of_zero`), so `K (1/t) = √t · K t`.  Substituting `Phi = (K - 1)/2`
gives exactly the theta-inversion law of `C3_theta_transformation`. -/
theorem C3_theta_transformation_at_Phi : C3_theta_transformation Phi := by
  intro t ht
  have hK : evenKernel 0 (1 / t) = Real.sqrt t * evenKernel 0 t := by
    have hfe := evenKernel_functional_equation 0 t
    rw [← evenKernel_eq_cosKernel_of_zero, ← Real.sqrt_eq_rpow] at hfe
    have hs : Real.sqrt t ≠ 0 := ne_of_gt (Real.sqrt_pos.2 ht)
    have h2 : Real.sqrt t * evenKernel 0 t = evenKernel 0 (1 / t) := by
      rw [hfe]; field_simp
    exact h2.symm
  simp only [Phi]
  push_cast [hK]
  ring

/-- **C₅-INPUT at Φ — PROVED.**  The spectrum is `μ n = n²` — real, non-negative — and Mathlib's
`hasSum_int_evenKernel` says exactly that its heat trace is the kernel:
`∑_{n : ℤ} exp (-π n² t) = evenKernel 0 t = 2 · Phi t + 1`.  The SPECTRAL INPUT is therefore
certified at the fixed witness.  (The spectral OUTPUT — that this spectrum is a self-adjoint
operator's, with the zeros as eigenvalues — is `C5_output`, and is NOT claimed: see its docstring.
The distance between the two is the premise's fifth register.) -/
theorem C5_input_at_Phi : C5_input Phi := by
  refine ⟨fun n : ℤ => (n : ℝ) ^ 2, fun n => sq_nonneg _, ?_⟩
  intro t ht
  have h := hasSum_int_evenKernel 0 ht
  have h2 : (2 : ℂ) * Phi t + 1 = ((evenKernel 0 t : ℝ) : ℂ) := by
    simp only [Phi]; ring
  rw [h2]
  have h3 := Complex.hasSum_ofReal.2 h
  simpa using h3

/-- **C₇-ENTIRETY at Φ — PROVED.**  `G = completedRiemannZeta₀` is entire
(`differentiable_completedZeta₀`), and on `1 < re s` Mathlib's `completedRiemannZeta_eq` gives
`Λ s = Λ₀ s - 1/s - 1/(1-s)`, i.e. `Λ₀ s = Λ s + 1/s + 1/(1-s)`; T1/T2 identify `Λ s` with
`mellin Phi (s/2)`.  So the completed Mellin transform of the fixed witness continues to an entire
function — the object Hadamard would factor exists. -/
theorem C7_entirety_at_Phi : C7_entirety Phi := by
  refine ⟨completedRiemannZeta₀, differentiable_completedZeta₀, ?_⟩
  intro s hs
  have h := completedRiemannZeta_eq s
  have hm := completedRiemannZeta_eq_mellinPhi s hs
  rw [← hm]
  rw [h]
  ring

/-- **C₇-ORDER at Φ — OPEN.**  The order-≤1 (maximal-type) growth bound on the entire completion,
`‖G s‖ ≤ C · exp (A · ‖s‖ · log (‖s‖ + 2))`.  See `C7_order`'s docstring for the price and for the
2026-07-14 correction of the statement's form (the earlier finite-exponential-type form was false of
the forced witness — W-8 sitting-1 STOP).  The statement is carried openly; it is not weakened.

Truth-plausibility screen (2026-07-14, per the standing rule).  Forced witness
`G = completedRiemannZeta₀` (pinned by the entirety conjunct + the identity theorem).  The corrected
order-≤1 / maximal-type bound **holds** of it — the Γ real-axis growth `exp(½ σ log σ)` sits inside
this form, and genus-1 Hadamard consumes order ≤ 1.  The old finite-type form did **not** hold of the
same witness; that is why it was corrected, not merely left open. -/
theorem C7_order_at_Phi : C7_order Phi := by
  sorry -- OPEN: needs (1) complex-Stirling bound ‖Γ(s/2)‖ ≤ exp(A‖s‖ log‖s‖) — Mathlib has NO norm
        -- bound on Complex.Gamma and no Gamma/Stirling file; (2) finite order of ζ in the strip via
        -- PhragmenLindelof.vertical_strip (a maximum principle — a tool, not the ingredient).
        -- Statement CORRECTED 2026-07-14 to true order ≤ 1 (was false finite-type — W-8 STOP).

/-! ## What C₄ and C₅ are, and are not

`C4_modularity` and `C5_heat_trace` are STATED ONLY.  No theorem in this file claims them at
`Phi`, and none should until the statements are argued in the manuscript layer: C₅ in particular
asserts a *specific* spectral realisation, which the programme explicitly does NOT claim (see the
Misreadings appendix of EXCLUSION_ENGINE: the spectral kernels disclaim Hilbert–Pólya rather than
rest on it).  Writing `C5_heat_trace Phi` as a theorem would be an overclaim.
-/

/-! ## The n = 1 binding instance of the channel inequality

From the bench (BALANCE_AND_POSITIVITY Appendix B):

  λ_A(1) = 1 - γ/2 - log 2 - (1/2) log π          (= -0.554119955935…)
  λ_Z(1) = γ                                       (= +0.577215664902…)

so the joint's n = 1 instance `λ_Z(1) ≥ -λ_A(1)` is *exactly* the constants inequality

  **γ + 2 ≥ log (4 π)**          (slack = 2 λ₁ = 0.0461914179…)

NOTE — CORRECTION OF THE WORK-ORDER.  The O.18 sitting proposed this as `3γ + 2 ≥ log (4π)`.
That is a true inequality but it is NOT the n = 1 instance: its slack is 1.2006…, whereas the
n = 1 instance has slack exactly `2 λ₁ = 0.046191…`.  The correct constants form is `γ + 2 ≥
log (4π)`, verified against the bench to 15 digits.  It is stated below.

WHY IT IS NOT PROVED HERE.  It needs `γ ≥ log (4π) - 2 = 0.53102…`.  Mathlib's available bounds
are `one_half_lt_eulerMascheroniConstant : 1/2 < γ` and `eulerMascheroniConstant_lt_two_thirds`,
and `1/2 < γ` is NOT sharp enough (0.5 < 0.53102).  A sharper lower bound is derivable from
`eulerMascheroniSeq_lt_eulerMascheroniConstant` plus numeric bounds on `log`, but that is a
numeric-analysis exercise, not a transport of the premise, and it is left as its own obligation
rather than asserted. -/
theorem n_one_binding_instance :
    Real.eulerMascheroniConstant + 2 ≥ Real.log (4 * Real.pi) := by
  sorry -- OPEN: needs γ ≥ 0.53102…; Mathlib's `1/2 < γ` is not sharp enough. See the note above.

end SIDELvConservation
