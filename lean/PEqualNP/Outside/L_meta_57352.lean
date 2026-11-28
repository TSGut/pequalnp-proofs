import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_57352 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2197427 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  let C : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [2, 3]⟩, ⟨.not, [6]⟩, ⟨.and, [0, 7]⟩, ⟨.and, [2, 4]⟩, ⟨.or, [9, 8]⟩, ⟨.not, [5]⟩, ⟨.or, [4, 0]⟩, ⟨.not, [12]⟩, ⟨.and, [3, 13]⟩, ⟨.or, [1, 14]⟩, ⟨.and, [15, 11]⟩, ⟨.or, [16, 10]⟩], 17⟩
  refine ⟨C, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp [C] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h <;> subst g <;> simp
