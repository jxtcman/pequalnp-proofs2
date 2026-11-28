import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54593 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1948407 : ℕ).testBit (6 * u.val + v.val)) 12 := by
  refine ⟨⟨[⟨.or, [2, 9]⟩, ⟨.or, [3, 0]⟩, ⟨.or, [8, 1]⟩, ⟨.or, [7, 0]⟩, ⟨.or, [12, 13]⟩, ⟨.and, [10, 14]⟩, ⟨.and, [11, 6]⟩, ⟨.or, [16, 5]⟩, ⟨.and, [13, 12]⟩, ⟨.or, [4, 15]⟩, ⟨.or, [19, 17]⟩, ⟨.or, [18, 20]⟩], 21⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
