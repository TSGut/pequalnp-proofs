import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_57605 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (270551467 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  let C : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [1, 2]⟩, ⟨.or, [4, 6]⟩, ⟨.and, [3, 7]⟩, ⟨.or, [0, 5]⟩, ⟨.or, [6, 0]⟩, ⟨.not, [10]⟩, ⟨.or, [2, 11]⟩, ⟨.and, [12, 9]⟩, ⟨.or, [13, 8]⟩, ⟨.and, [4, 10]⟩, ⟨.or, [15, 14]⟩, ⟨.not, [16]⟩], 17⟩
  refine ⟨C, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp [C] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h <;> subst g <;> simp
