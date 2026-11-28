import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_58096 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 13 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (4344510 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  let C : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.and, [4, 3]⟩, ⟨.or, [1, 3]⟩, ⟨.or, [7, 4]⟩, ⟨.not, [8]⟩, ⟨.and, [2, 9]⟩, ⟨.or, [2, 4]⟩, ⟨.not, [11]⟩, ⟨.and, [1, 12]⟩, ⟨.or, [8, 5]⟩, ⟨.and, [0, 14]⟩, ⟨.or, [15, 13]⟩, ⟨.or, [16, 10]⟩, ⟨.or, [17, 6]⟩], 18⟩
  refine ⟨C, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp [C] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst g <;> simp
