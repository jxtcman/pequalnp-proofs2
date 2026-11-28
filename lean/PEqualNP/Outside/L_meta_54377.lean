import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54377 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (320952 : ℕ).testBit (6 * u.val + v.val)) 11 := by
  refine ⟨⟨[⟨.or, [7, 1]⟩, ⟨.or, [2, 8]⟩, ⟨.or, [11, 9]⟩, ⟨.and, [10, 11]⟩, ⟨.or, [13, 0]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [6, 14]⟩, ⟨.or, [5, 16]⟩, ⟨.and, [3, 4]⟩, ⟨.and, [17, 15]⟩, ⟨.or, [19, 18]⟩], 20⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
