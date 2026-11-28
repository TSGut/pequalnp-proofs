import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_58073 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 13 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (4311210 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  let C : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [5, 1]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [0, 7]⟩, ⟨.and, [4, 7]⟩, ⟨.or, [2, 9]⟩, ⟨.or, [3, 10]⟩, ⟨.not, [11]⟩, ⟨.and, [1, 12]⟩, ⟨.or, [6, 0]⟩, ⟨.not, [14]⟩, ⟨.and, [10, 15]⟩, ⟨.or, [16, 13]⟩, ⟨.or, [17, 8]⟩], 18⟩
  refine ⟨C, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp [C] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst g <;> simp
