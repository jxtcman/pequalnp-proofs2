import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_53695 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (275389 : ℕ).testBit (6 * u.val + v.val)) 12 := by
  refine ⟨⟨[⟨.or, [7, 2]⟩, ⟨.or, [10, 6]⟩, ⟨.or, [3, 11]⟩, ⟨.or, [5, 0]⟩, ⟨.or, [4, 1]⟩, ⟨.or, [8, 14]⟩, ⟨.and, [14, 12]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [17, 15]⟩, ⟨.or, [16, 13]⟩, ⟨.and, [19, 18]⟩, ⟨.or, [4, 20]⟩], 20⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
