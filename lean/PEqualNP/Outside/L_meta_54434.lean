import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54434 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (320953 : ℕ).testBit (6 * u.val + v.val)) 12 := by
  refine ⟨⟨[⟨.or, [2, 8]⟩, ⟨.and, [4, 3]⟩, ⟨.or, [1, 7]⟩, ⟨.or, [4, 10]⟩, ⟨.or, [6, 0]⟩, ⟨.or, [9, 13]⟩, ⟨.or, [14, 5]⟩, ⟨.or, [16, 10]⟩, ⟨.and, [15, 16]⟩, ⟨.and, [12, 17]⟩, ⟨.or, [18, 19]⟩, ⟨.or, [11, 20]⟩], 21⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
