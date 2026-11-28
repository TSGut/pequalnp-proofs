import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_57346 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2197298 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  let C : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [1, 4]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [0, 7]⟩, ⟨.and, [4, 1]⟩, ⟨.or, [9, 8]⟩, ⟨.and, [6, 2]⟩, ⟨.or, [11, 10]⟩, ⟨.or, [5, 4]⟩, ⟨.or, [0, 13]⟩, ⟨.not, [14]⟩, ⟨.and, [3, 15]⟩, ⟨.or, [16, 12]⟩], 17⟩
  refine ⟨C, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp [C] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h <;> subst g <;> simp
