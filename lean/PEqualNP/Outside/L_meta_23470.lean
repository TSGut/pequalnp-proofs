import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

private def witness23470 : Circuit :=
  ⟨[⟨.and, [0, 1]⟩, ⟨.not, [0]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [7, 8]⟩, ⟨.or, [6, 9]⟩, ⟨.or, [5, 10]⟩, ⟨.or, [4, 11]⟩, ⟨.not, [12]⟩], 13⟩

theorem PEqualNP.Outside.L_meta_23470 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (141 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨witness23470, ?_, by decide, by decide +kernel⟩
  intro gate membership
  simp [witness23470] at membership
  rcases membership with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
