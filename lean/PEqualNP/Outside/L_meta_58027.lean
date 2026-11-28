import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_58027 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 13 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2198839 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  let C : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [0, 5]⟩, ⟨.or, [4, 6]⟩, ⟨.or, [1, 7]⟩, ⟨.not, [8]⟩, ⟨.and, [3, 9]⟩, ⟨.not, [3]⟩, ⟨.and, [0, 11]⟩, ⟨.or, [1, 4]⟩, ⟨.and, [2, 13]⟩, ⟨.or, [14, 12]⟩, ⟨.and, [7, 1]⟩, ⟨.or, [16, 15]⟩, ⟨.or, [17, 10]⟩], 18⟩
  refine ⟨C, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp [C] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst g <;> simp
