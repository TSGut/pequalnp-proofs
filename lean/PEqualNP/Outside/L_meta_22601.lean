import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

private def witness : Circuit :=
  ⟨[⟨.or, [2, 3]⟩, ⟨.or, [0, 10]⟩, ⟨.and, [5, 11]⟩, ⟨.and, [6, 10]⟩,
    ⟨.or, [0, 1]⟩, ⟨.and, [9, 14]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [2, 14]⟩,
    ⟨.and, [16, 17]⟩, ⟨.or, [4, 12]⟩, ⟨.or, [13, 19]⟩, ⟨.or, [15, 20]⟩,
    ⟨.or, [18, 21]⟩], 22⟩

theorem PEqualNP.Outside.L_meta_22601 :
    PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1965691 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  refine ⟨witness, ?_, by decide, by decide +kernel⟩
  intro gate membership
  simp [witness] at membership
  rcases membership with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl <;> simp
