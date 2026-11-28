import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54399 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (327094 : ℕ).testBit (6 * u.val + v.val)) 11 := by
  refine ⟨⟨[⟨.or, [6, 5]⟩, ⟨.or, [1, 4]⟩, ⟨.or, [7, 10]⟩, ⟨.or, [11, 0]⟩, ⟨.or, [2, 10]⟩, ⟨.or, [9, 14]⟩, ⟨.and, [12, 2]⟩, ⟨.or, [13, 16]⟩, ⟨.or, [3, 15]⟩, ⟨.or, [8, 18]⟩, ⟨.and, [19, 17]⟩], 20⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
