import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_58042 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 13 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2215223 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  let C : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [4, 5]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [7, 4]⟩, ⟨.or, [8, 6]⟩, ⟨.not, [9]⟩, ⟨.and, [2, 8]⟩, ⟨.or, [11, 10]⟩, ⟨.not, [3]⟩, ⟨.and, [0, 13]⟩, ⟨.or, [14, 12]⟩, ⟨.and, [6, 7]⟩, ⟨.or, [16, 15]⟩, ⟨.or, [17, 10]⟩], 18⟩
  refine ⟨C, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp [C] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst g <;> simp
