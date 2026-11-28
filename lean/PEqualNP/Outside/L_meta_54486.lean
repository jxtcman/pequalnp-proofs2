import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54486 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (808554 : ℕ).testBit (6 * u.val + v.val)) 12 := by
  refine ⟨⟨[⟨.or, [7, 3]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [10, 2]⟩, ⟨.or, [5, 1]⟩, ⟨.or, [4, 0]⟩, ⟨.or, [9, 13]⟩, ⟨.and, [11, 13]⟩, ⟨.and, [2, 6]⟩, ⟨.or, [15, 12]⟩, ⟨.or, [16, 14]⟩, ⟨.or, [17, 19]⟩, ⟨.and, [18, 20]⟩], 21⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
