import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_57972 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 13 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2181036 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  let C : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [3, 5]⟩, ⟨.and, [0, 6]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [4, 9]⟩, ⟨.or, [10, 8]⟩, ⟨.not, [11]⟩, ⟨.or, [12, 7]⟩, ⟨.and, [1, 4]⟩, ⟨.or, [14, 13]⟩, ⟨.not, [6]⟩, ⟨.and, [2, 16]⟩, ⟨.or, [17, 15]⟩], 18⟩
  refine ⟨C, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp [C] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst g <;> simp
