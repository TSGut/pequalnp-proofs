import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

private def witness : Circuit :=
  ⟨[⟨.and, [2, 3]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [4, 7]⟩, ⟨.not, [8]⟩,
    ⟨.or, [0, 9]⟩], 10⟩

theorem PEqualNP.Outside.L_meta_23254 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2114495 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨witness, ?_, by decide, by decide +kernel⟩
  intro gate membership
  simp [witness] at membership
  rcases membership with rfl | rfl | rfl | rfl | rfl <;> simp
