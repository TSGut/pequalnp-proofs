import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_58153 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 13 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6409526 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  let C : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.and, [0, 1]⟩, ⟨.or, [0, 1]⟩, ⟨.and, [4, 7]⟩, ⟨.or, [8, 6]⟩, ⟨.not, [5]⟩, ⟨.and, [2, 10]⟩, ⟨.and, [5, 7]⟩, ⟨.or, [7, 5]⟩, ⟨.not, [13]⟩, ⟨.and, [3, 14]⟩, ⟨.or, [15, 12]⟩, ⟨.or, [16, 11]⟩, ⟨.or, [17, 9]⟩], 18⟩
  refine ⟨C, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp [C] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst g <;> simp
