import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_58024 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 13 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2198712 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  let C : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [1, 5]⟩, ⟨.or, [6, 4]⟩, ⟨.not, [7]⟩, ⟨.and, [8, 3]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [3, 10]⟩, ⟨.not, [11]⟩, ⟨.or, [4, 12]⟩, ⟨.and, [0, 5]⟩, ⟨.or, [14, 13]⟩, ⟨.or, [1, 10]⟩, ⟨.and, [16, 15]⟩, ⟨.or, [17, 9]⟩], 18⟩
  refine ⟨C, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp [C] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst g <;> simp
