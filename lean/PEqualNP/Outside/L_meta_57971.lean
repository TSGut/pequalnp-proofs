import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_57971 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 13 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2181034 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  let C : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.and, [0, 5]⟩, ⟨.or, [3, 0]⟩, ⟨.and, [4, 7]⟩, ⟨.or, [2, 5]⟩, ⟨.or, [9, 8]⟩, ⟨.not, [10]⟩, ⟨.or, [1, 3]⟩, ⟨.and, [12, 11]⟩, ⟨.or, [5, 7]⟩, ⟨.or, [11, 14]⟩, ⟨.not, [15]⟩, ⟨.or, [16, 13]⟩, ⟨.or, [17, 6]⟩], 18⟩
  refine ⟨C, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp [C] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst g <;> simp
