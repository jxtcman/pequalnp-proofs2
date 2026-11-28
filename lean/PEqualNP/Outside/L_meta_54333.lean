import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54333 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (288362 : ℕ).testBit (6 * u.val + v.val)) 11 := by
  refine ⟨⟨[⟨.or, [3, 9]⟩, ⟨.or, [2, 7]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [7, 14]⟩, ⟨.and, [15, 13]⟩, ⟨.or, [12, 6]⟩, ⟨.or, [11, 8]⟩, ⟨.and, [18, 17]⟩, ⟨.or, [16, 19]⟩], 20⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
