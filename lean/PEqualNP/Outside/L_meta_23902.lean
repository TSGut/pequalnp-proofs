import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_meta_23902 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (274910 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.and, [0, 4]⟩, ⟨.not, [4]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [1, 7]⟩, ⟨.and, [6, 8]⟩, ⟨.or, [5, 9]⟩], 10⟩, ?_, by decide, by decide +kernel⟩
  intro gate membership
  simp at membership
  rcases membership with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
