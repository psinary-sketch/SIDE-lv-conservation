import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.MellinTransform

/-! Smoke test to confirm the toolchain and Mathlib pin build against the
federation-shared packages/ junction. Kept minimal to isolate skeleton
issues from the T1/T2/T3 content. -/

namespace SIDELvConservation

open Complex

example : completedRiemannZeta 2 = completedRiemannZeta 2 := rfl

end SIDELvConservation
