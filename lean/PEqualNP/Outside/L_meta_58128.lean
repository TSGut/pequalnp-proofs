import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_58128 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 13 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6375865 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  let C : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [3, 0]⟩, ⟨.and, [4, 6]⟩, ⟨.or, [1, 0]⟩, ⟨.and, [8, 5]⟩, ⟨.or, [9, 7]⟩, ⟨.and, [2, 4]⟩, ⟨.or, [2, 1]⟩, ⟨.and, [12, 6]⟩, ⟨.or, [13, 4]⟩, ⟨.or, [5, 14]⟩, ⟨.not, [15]⟩, ⟨.or, [16, 11]⟩, ⟨.or, [17, 10]⟩], 18⟩
  refine ⟨C, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp [C] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst g <;> simp
