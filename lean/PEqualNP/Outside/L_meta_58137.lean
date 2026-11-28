import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_58137 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 13 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6376760 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  let C : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [1, 0]⟩, ⟨.and, [5, 6]⟩, ⟨.and, [4, 6]⟩, ⟨.or, [8, 7]⟩, ⟨.or, [0, 3]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [11, 10]⟩, ⟨.or, [5, 12]⟩, ⟨.not, [13]⟩, ⟨.and, [3, 14]⟩, ⟨.and, [2, 14]⟩, ⟨.or, [16, 15]⟩, ⟨.or, [17, 9]⟩], 18⟩
  refine ⟨C, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp [C] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst g <;> simp
