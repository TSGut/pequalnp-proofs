import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_53739 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (34110 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  let C : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [1, 3]⟩, ⟨.and, [2, 6]⟩, ⟨.and, [1, 4]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [4, 2]⟩, ⟨.or, [10, 9]⟩, ⟨.and, [0, 11]⟩, ⟨.or, [12, 8]⟩, ⟨.or, [13, 7]⟩], 14⟩
  refine ⟨C, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp [C] at hg
  rcases hg with h | h | h | h | h | h | h | h | h <;> subst g <;> simp
