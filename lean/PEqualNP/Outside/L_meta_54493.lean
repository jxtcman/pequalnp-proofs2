import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54493 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (808696 : ℕ).testBit (6 * u.val + v.val)) 12 := by
  refine ⟨⟨[⟨.or, [1, 3]⟩, ⟨.or, [4, 0]⟩, ⟨.or, [11, 1]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [10, 9]⟩, ⟨.or, [8, 2]⟩, ⟨.or, [6, 12]⟩, ⟨.or, [11, 5]⟩, ⟨.or, [7, 15]⟩, ⟨.and, [18, 16]⟩, ⟨.and, [13, 17]⟩, ⟨.or, [19, 20]⟩], 21⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
