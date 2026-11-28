import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54400 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (327103 : ℕ).testBit (6 * u.val + v.val)) 11 := by
  refine ⟨⟨[⟨.or, [3, 9]⟩, ⟨.or, [6, 5]⟩, ⟨.or, [10, 8]⟩, ⟨.or, [11, 4]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [13, 7]⟩, ⟨.or, [1, 4]⟩, ⟨.and, [14, 16]⟩, ⟨.and, [2, 15]⟩, ⟨.or, [18, 17]⟩, ⟨.or, [19, 0]⟩], 20⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
