import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54507 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (851325 : ℕ).testBit (6 * u.val + v.val)) 12 := by
  refine ⟨⟨[⟨.or, [0, 2]⟩, ⟨.or, [7, 6]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [10, 11]⟩, ⟨.or, [1, 0]⟩, ⟨.or, [4, 13]⟩, ⟨.or, [8, 6]⟩, ⟨.or, [9, 16]⟩, ⟨.and, [12, 5]⟩, ⟨.and, [17, 14]⟩, ⟨.or, [15, 19]⟩, ⟨.or, [18, 20]⟩], 21⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
