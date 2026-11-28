import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54533 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1867390 : ℕ).testBit (6 * u.val + v.val)) 12 := by
  refine ⟨⟨[⟨.or, [7, 2]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [6, 1]⟩, ⟨.or, [5, 12]⟩, ⟨.or, [10, 3]⟩, ⟨.or, [11, 13]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [14, 16]⟩, ⟨.and, [17, 15]⟩, ⟨.and, [13, 11]⟩, ⟨.and, [0, 16]⟩, ⟨.or, [18, 19]⟩], 21⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
