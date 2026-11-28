import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54441 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (322749 : ℕ).testBit (6 * u.val + v.val)) 12 := by
  refine ⟨⟨[⟨.or, [9, 8]⟩, ⟨.or, [2, 10]⟩, ⟨.or, [6, 1]⟩, ⟨.or, [5, 0]⟩, ⟨.or, [11, 13]⟩, ⟨.and, [13, 11]⟩, ⟨.or, [7, 15]⟩, ⟨.or, [12, 16]⟩, ⟨.or, [0, 3]⟩, ⟨.and, [18, 4]⟩, ⟨.and, [17, 14]⟩, ⟨.or, [20, 19]⟩], 21⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
