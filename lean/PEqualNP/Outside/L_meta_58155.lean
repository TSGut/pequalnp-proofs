import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_58155 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 13 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6409657 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  let C : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.and, [1, 5]⟩, ⟨.and, [1, 3]⟩, ⟨.or, [0, 7]⟩, ⟨.or, [1, 2]⟩, ⟨.not, [9]⟩, ⟨.and, [10, 8]⟩, ⟨.or, [11, 6]⟩, ⟨.or, [5, 8]⟩, ⟨.not, [13]⟩, ⟨.or, [9, 3]⟩, ⟨.and, [15, 14]⟩, ⟨.or, [16, 12]⟩], 17⟩
  refine ⟨C, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp [C] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h <;> subst g <;> simp
