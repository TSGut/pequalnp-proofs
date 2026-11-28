import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_58116 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 13 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6374833 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  let C : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [1, 2]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [7, 5]⟩, ⟨.not, [8]⟩, ⟨.and, [3, 9]⟩, ⟨.or, [3, 0]⟩, ⟨.or, [11, 5]⟩, ⟨.not, [12]⟩, ⟨.or, [3, 6]⟩, ⟨.not, [14]⟩, ⟨.or, [15, 13]⟩, ⟨.and, [7, 16]⟩, ⟨.or, [17, 10]⟩], 18⟩
  refine ⟨C, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp [C] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst g <;> simp
