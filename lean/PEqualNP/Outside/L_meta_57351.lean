import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_57351 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2197424 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  let C : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [1, 3]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [0, 7]⟩, ⟨.not, [8]⟩, ⟨.or, [2, 9]⟩, ⟨.and, [10, 6]⟩, ⟨.and, [4, 10]⟩, ⟨.and, [0, 7]⟩, ⟨.or, [13, 12]⟩, ⟨.or, [14, 11]⟩, ⟨.and, [1, 4]⟩, ⟨.or, [16, 15]⟩], 17⟩
  refine ⟨C, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp [C] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h <;> subst g <;> simp
