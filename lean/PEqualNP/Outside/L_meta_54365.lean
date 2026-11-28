import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54365 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (292589 : ℕ).testBit (6 * u.val + v.val)) 10 := by
  refine ⟨⟨[⟨.or, [7, 2]⟩, ⟨.or, [6, 1]⟩, ⟨.or, [0, 5]⟩, ⟨.or, [10, 8]⟩, ⟨.or, [10, 9]⟩, ⟨.and, [13, 11]⟩, ⟨.or, [11, 14]⟩, ⟨.or, [15, 12]⟩, ⟨.and, [16, 17]⟩, ⟨.or, [4, 18]⟩], 19⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
