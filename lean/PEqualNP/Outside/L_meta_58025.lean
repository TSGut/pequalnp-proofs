import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_58025 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 13 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2198717 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  let C : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [5, 4]⟩, ⟨.or, [0, 3]⟩, ⟨.not, [7]⟩, ⟨.or, [8, 6]⟩, ⟨.or, [1, 9]⟩, ⟨.not, [10]⟩, ⟨.not, [2]⟩, ⟨.and, [1, 12]⟩, ⟨.and, [2, 4]⟩, ⟨.or, [0, 14]⟩, ⟨.or, [15, 13]⟩, ⟨.and, [16, 9]⟩, ⟨.or, [17, 11]⟩], 18⟩
  refine ⟨C, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp [C] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst g <;> simp
