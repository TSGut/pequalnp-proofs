import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_58026 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 13 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2198718 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  let C : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [3, 2]⟩, ⟨.not, [6]⟩, ⟨.and, [7, 1]⟩, ⟨.or, [4, 0]⟩, ⟨.and, [9, 2]⟩, ⟨.or, [10, 8]⟩, ⟨.or, [4, 1]⟩, ⟨.or, [5, 12]⟩, ⟨.not, [13]⟩, ⟨.and, [3, 14]⟩, ⟨.and, [0, 13]⟩, ⟨.or, [16, 15]⟩, ⟨.or, [17, 11]⟩], 18⟩
  refine ⟨C, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp [C] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst g <;> simp
