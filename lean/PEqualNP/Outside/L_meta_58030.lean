import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_58030 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 13 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2198972 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  let C : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [4, 5]⟩, ⟨.or, [1, 6]⟩, ⟨.not, [7]⟩, ⟨.and, [3, 8]⟩, ⟨.or, [4, 3]⟩, ⟨.or, [0, 10]⟩, ⟨.not, [11]⟩, ⟨.or, [6, 12]⟩, ⟨.or, [0, 1]⟩, ⟨.and, [14, 13]⟩, ⟨.and, [2, 11]⟩, ⟨.or, [16, 15]⟩, ⟨.or, [17, 9]⟩], 18⟩
  refine ⟨C, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp [C] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst g <;> simp
