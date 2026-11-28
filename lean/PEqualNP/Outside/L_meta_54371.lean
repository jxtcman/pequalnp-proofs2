import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54371 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (294458 : ℕ).testBit (6 * u.val + v.val)) 11 := by
  refine ⟨⟨[⟨.or, [9, 8]⟩, ⟨.or, [4, 0]⟩, ⟨.or, [1, 6]⟩, ⟨.or, [2, 10]⟩, ⟨.or, [5, 11]⟩, ⟨.or, [5, 3]⟩, ⟨.or, [7, 13]⟩, ⟨.or, [12, 14]⟩, ⟨.and, [16, 17]⟩, ⟨.and, [15, 11]⟩, ⟨.or, [18, 19]⟩], 20⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
