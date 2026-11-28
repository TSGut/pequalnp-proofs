import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_57347 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2197299 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  let C : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [0, 4]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [7, 6]⟩, ⟨.or, [0, 3]⟩, ⟨.or, [1, 9]⟩, ⟨.or, [6, 5]⟩, ⟨.and, [7, 11]⟩, ⟨.not, [12]⟩, ⟨.and, [13, 10]⟩, ⟨.and, [14, 8]⟩, ⟨.and, [4, 2]⟩, ⟨.or, [16, 15]⟩], 17⟩
  refine ⟨C, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp [C] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h <;> subst g <;> simp
