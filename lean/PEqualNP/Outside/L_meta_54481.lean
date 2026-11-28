import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54481 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (808494 : ℕ).testBit (6 * u.val + v.val)) 12 := by
  refine ⟨⟨[⟨.or, [7, 8]⟩, ⟨.and, [1, 10]⟩, ⟨.or, [5, 2]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [12, 14]⟩, ⟨.or, [9, 12]⟩, ⟨.or, [13, 15]⟩, ⟨.or, [16, 7]⟩, ⟨.or, [18, 14]⟩, ⟨.and, [19, 17]⟩, ⟨.or, [20, 11]⟩], 21⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
