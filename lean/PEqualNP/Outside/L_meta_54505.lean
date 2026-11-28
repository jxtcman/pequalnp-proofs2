import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54505 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (851321 : ℕ).testBit (6 * u.val + v.val)) 12 := by
  refine ⟨⟨[⟨.or, [7, 1]⟩, ⟨.or, [6, 0]⟩, ⟨.or, [8, 2]⟩, ⟨.or, [5, 10]⟩, ⟨.or, [11, 13]⟩, ⟨.and, [5, 3]⟩, ⟨.and, [10, 11]⟩, ⟨.or, [15, 16]⟩, ⟨.or, [17, 4]⟩, ⟨.or, [9, 12]⟩, ⟨.and, [19, 14]⟩, ⟨.or, [20, 18]⟩], 21⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
