import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_57964 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 13 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2180907 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  let C : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [2, 4]⟩, ⟨.and, [5, 3]⟩, ⟨.or, [7, 6]⟩, ⟨.not, [8]⟩, ⟨.or, [1, 9]⟩, ⟨.or, [0, 3]⟩, ⟨.or, [6, 11]⟩, ⟨.and, [12, 10]⟩, ⟨.or, [5, 11]⟩, ⟨.not, [2]⟩, ⟨.or, [15, 14]⟩, ⟨.not, [16]⟩, ⟨.or, [17, 13]⟩], 18⟩
  refine ⟨C, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp [C] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst g <;> simp
