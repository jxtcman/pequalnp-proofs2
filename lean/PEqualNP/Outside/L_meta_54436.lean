import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54436 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (320999 : ℕ).testBit (6 * u.val + v.val)) 12 := by
  refine ⟨⟨[⟨.or, [6, 5]⟩, ⟨.or, [10, 4]⟩, ⟨.or, [11, 8]⟩, ⟨.and, [4, 3]⟩, ⟨.or, [9, 11]⟩, ⟨.and, [12, 1]⟩, ⟨.or, [10, 7]⟩, ⟨.and, [0, 14]⟩, ⟨.or, [15, 17]⟩, ⟨.and, [2, 16]⟩, ⟨.or, [18, 19]⟩, ⟨.or, [20, 13]⟩], 21⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
