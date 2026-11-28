import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54502 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (851259 : ℕ).testBit (6 * u.val + v.val)) 12 := by
  refine ⟨⟨[⟨.or, [5, 4]⟩, ⟨.or, [2, 8]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [10, 7]⟩, ⟨.and, [3, 10]⟩, ⟨.or, [13, 1]⟩, ⟨.or, [9, 11]⟩, ⟨.and, [16, 12]⟩, ⟨.or, [14, 12]⟩, ⟨.or, [16, 18]⟩, ⟨.or, [15, 17]⟩, ⟨.and, [19, 20]⟩], 21⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
