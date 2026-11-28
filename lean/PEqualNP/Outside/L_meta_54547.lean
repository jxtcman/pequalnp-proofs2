import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54547 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1881588 : ℕ).testBit (6 * u.val + v.val)) 12 := by
  refine ⟨⟨[⟨.or, [8, 6]⟩, ⟨.or, [0, 5]⟩, ⟨.or, [1, 3]⟩, ⟨.or, [12, 9]⟩, ⟨.or, [2, 10]⟩, ⟨.or, [7, 1]⟩, ⟨.or, [4, 11]⟩, ⟨.or, [16, 15]⟩, ⟨.or, [16, 6]⟩, ⟨.and, [17, 14]⟩, ⟨.and, [13, 18]⟩, ⟨.or, [19, 20]⟩], 21⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
