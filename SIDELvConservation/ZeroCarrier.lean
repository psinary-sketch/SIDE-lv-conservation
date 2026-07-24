import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Topology.DiscreteSubset

/-!
# W-ORD-P1-FINSET — chunk (a): the entire carrier for the nontrivial ζ-zeros

Prerequisite construction for discharging the finite-set conjunct of
`PartialPositivity.ExplicitFormulaDecomp`.  Mathlib's `completedRiemannZeta₀` (Λ₀) is entire but
its zeros are **not** the nontrivial ζ-zeros (`Λ = Λ₀ − 1/s − 1/(1−s)`, so ζ-zeros are Λ-zeros,
not Λ₀-zeros).  This file builds an **entire** function `xiCarrier` whose zeros **in the open
critical strip** coincide exactly with the nontrivial ζ-zeros, so that the later isolated-zeros /
compactness argument (chunk b) can run on a compact box that touches the pole points `s = 0, 1`.

Closed form (survey-scope correction to the work-order's rough `−(2s−1)`):
`xiCarrier s = s·(s−1)·Λ₀(s) + 1`, which agrees with `s·(s−1)·Λ(s)` off `{0, 1}` and hence with
`s·(s−1)·Gammaℝ(s)·ζ(s)` on the strip.  Grade: DERIVES (all ingredients Mathlib-present at pin
5e932f97); no `sorry`.
-/

namespace SIDELvConservation
namespace PartialPositivity

open Complex Filter Topology

/-- **Entire carrier for the nontrivial ζ-zeros.**  `xiCarrier s = s·(s−1)·Λ₀(s) + 1`.
Manifestly entire (`differentiable_completedZeta₀` + polynomial parts); agrees with
`s·(s−1)·Λ(s)` off `{0,1}` (see `xiCarrier_eq_mul_completed`). -/
noncomputable def xiCarrier (s : ℂ) : ℂ :=
  s * (s - 1) * completedRiemannZeta₀ s + 1

/-- `xiCarrier` is entire. -/
lemma differentiable_xiCarrier : Differentiable ℂ xiCarrier := by
  show Differentiable ℂ (fun s : ℂ => s * (s - 1) * completedRiemannZeta₀ s + 1)
  exact ((differentiable_id.mul (differentiable_id.sub_const 1)).mul
    differentiable_completedZeta₀).add_const 1

/-- Off the pole points `{0,1}`, the carrier equals `s·(s−1)·Λ(s)`.
Uses `completedRiemannZeta_eq : Λ = Λ₀ − 1/s − 1/(1−s)`; the `1/s`, `1/(1−s)` terms contribute
exactly the additive `+1`. -/
lemma xiCarrier_eq_mul_completed {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    s * (s - 1) * completedRiemannZeta s = xiCarrier s := by
  have hs1 : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  rw [completedRiemannZeta_eq, xiCarrier]
  field_simp
  ring

/-- Strip form: on `{s ≠ 0, s ≠ 1}` with `Gammaℝ s ≠ 0`, the carrier factors as
`s·(s−1)·Gammaℝ(s)·ζ(s)` — the shape that reads off the ζ-zeros. -/
lemma xiCarrier_zeta_form {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) (hG : Gammaℝ s ≠ 0) :
    xiCarrier s = s * (s - 1) * Gammaℝ s * riemannZeta s := by
  have hcomp : completedRiemannZeta s = riemannZeta s * Gammaℝ s := by
    rw [riemannZeta_def_of_ne_zero h0]; field_simp
  rw [← xiCarrier_eq_mul_completed h0 h1, hcomp]; ring

/-- **Strip zero-equivalence.**  On the open critical strip `0 < Re s < 1`, the carrier vanishes
exactly at the nontrivial ζ-zeros. -/
lemma xiCarrier_eq_zero_iff_riemannZeta {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    xiCarrier s = 0 ↔ riemannZeta s = 0 := by
  have hne0 : s ≠ 0 := by rintro rfl; simp at h0
  have hne1 : s ≠ 1 := by rintro rfl; norm_num at h1
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hne1
  have hG : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos h0
  rw [xiCarrier_zeta_form hne0 hne1 hG, mul_eq_zero, mul_eq_zero, mul_eq_zero]
  constructor
  · rintro (((h | h) | h) | h)
    · exact absurd h hne0
    · exact absurd h hsub
    · exact absurd h hG
    · exact h
  · intro h; exact Or.inr h

/-- **Non-vanishing witness** excluding `analyticOrderAt = ⊤` on connected ℂ (chunk b input).
For `Re s > 1` the carrier is nonzero, via `riemannZeta_ne_zero_of_one_lt_re` pushed through the
strip form. -/
lemma xiCarrier_ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) : xiCarrier s ≠ 0 := by
  have h0 : (0 : ℝ) < s.re := by linarith
  have hne0 : s ≠ 0 := by rintro rfl; simp at h0
  have hne1 : s ≠ 1 := by rintro rfl; norm_num at hs
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hne1
  have hG : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos h0
  have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  rw [xiCarrier_zeta_form hne0 hne1 hG]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hne0 hsub) hG) hz

/-! ### Chunk (b): finiteness of the carrier's zeros on a compact box, and of the ζ-zeros. -/

/-- **Locally-finite ∩ compact ⇒ finite** (set-level).  If every point of a compact `K` has a
neighbourhood meeting `Z` in a finite set, then `K ∩ Z` is finite.  Proved by a finite subcover
(`IsCompact.elim_nhds_subcover`) and a finite union of finite pieces. -/
lemma finite_inter_of_locallyFinite {Z K : Set ℂ} (hK : IsCompact K)
    (hZ : ∀ z ∈ K, ∃ t ∈ 𝓝 z, (t ∩ Z).Finite) : (K ∩ Z).Finite := by
  choose! U hUmem hUfin using hZ
  obtain ⟨tt, htt, hcov⟩ := hK.elim_nhds_subcover U hUmem
  have hbU : (⋃ x ∈ tt, (U x ∩ Z)).Finite :=
    tt.finite_toSet.biUnion (fun x hx => hUfin x (htt x (Finset.mem_coe.mp hx)))
  refine hbU.subset ?_
  intro s hs
  obtain ⟨hsK, hsZ⟩ := hs
  obtain ⟨x, hx, hsx⟩ := Set.mem_iUnion₂.mp (hcov hsK)
  exact Set.mem_iUnion₂.mpr ⟨x, hx, hsx, hsZ⟩

/-- The carrier's zero set meets any compact set in a finite set.  Route: `xiCarrier` entire
(`differentiable_xiCarrier` → `analyticOnNhd`), not identically zero (witness at `s = 2`, via
`xiCarrier_ne_zero_of_one_lt_re`), so its zero set is codiscrete
(`preimage_zero_mem_codiscreteWithin`), hence locally finite
(`codiscreteWithin_iff_locallyFiniteComplementWithin`), hence finite on the compact set. -/
lemma finite_carrier_zeros_inter_compact {K : Set ℂ} (hK : IsCompact K) :
    (K ∩ xiCarrier ⁻¹' {0}).Finite := by
  have hA : AnalyticOnNhd ℂ xiCarrier Set.univ :=
    (differentiable_xiCarrier.differentiableOn).analyticOnNhd isOpen_univ
  have hwit : xiCarrier 2 ≠ 0 :=
    xiCarrier_ne_zero_of_one_lt_re (by norm_num [Complex.re_ofNat])
  have hcod : xiCarrier ⁻¹' {0}ᶜ ∈ codiscreteWithin (Set.univ : Set ℂ) :=
    hA.preimage_zero_mem_codiscreteWithin hwit (Set.mem_univ 2) isConnected_univ
  have hLF := codiscreteWithin_iff_locallyFiniteComplementWithin.mp hcod
  refine finite_inter_of_locallyFinite hK ?_
  intro z _
  obtain ⟨t, ht, hfin⟩ := hLF z (Set.mem_univ z)
  refine ⟨t, ht, ?_⟩
  have hset : Set.univ \ xiCarrier ⁻¹' {0}ᶜ = xiCarrier ⁻¹' {0} := by
    ext x; simp
  rwa [hset] at hfin

/-- **Chunk (b) TARGET.**  There are only finitely many nontrivial ζ-zeros in the strip box
`{0 < Re s < 1, |Im s| ≤ T}`.  Transfers `finite_carrier_zeros_inter_compact` on the compact box
`[0,1] ×ℂ [-T,T]` to the ζ-zeros via the strip zero-equivalence `xiCarrier_eq_zero_iff_riemannZeta`.
Input to chunk (c)'s `Finset` / `NontrivialZero` transfer. -/
theorem finite_strip_box_riemannZeta_zeros (T : ℝ) :
    {s : ℂ | 0 < s.re ∧ s.re < 1 ∧ |s.im| ≤ T ∧ riemannZeta s = 0}.Finite := by
  have hK : IsCompact (Set.Icc (0 : ℝ) 1 ×ℂ Set.Icc (-T) T) :=
    isCompact_Icc.reProdIm isCompact_Icc
  refine (finite_carrier_zeros_inter_compact hK).subset ?_
  intro s hs
  obtain ⟨h0, h1, hT, hz⟩ := hs
  refine ⟨?_, ?_⟩
  · rw [mem_reProdIm]
    exact ⟨Set.mem_Icc.mpr ⟨h0.le, h1.le⟩, Set.mem_Icc.mpr (abs_le.mp hT)⟩
  · simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact (xiCarrier_eq_zero_iff_riemannZeta h0 h1).mpr hz

end PartialPositivity
end SIDELvConservation
