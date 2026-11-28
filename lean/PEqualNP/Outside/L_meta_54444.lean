import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54444 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (322814 : ℕ).testBit (6 * u.val + v.val)) 12 := by
  refine ⟨⟨[⟨.or, [7, 1]⟩, ⟨.or, [8, 5]⟩, ⟨.or, [4, 0]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [6, 5]⟩, ⟨.or, [9, 11]⟩, ⟨.and, [15, 13]⟩, ⟨.or, [2, 12]⟩, ⟨.or, [3, 14]⟩, ⟨.or, [18, 10]⟩, ⟨.and, [17, 19]⟩, ⟨.or, [20, 16]⟩], 21⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
