import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54408 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (291830 : ℕ).testBit (6 * u.val + v.val)) 12 := by
  refine ⟨⟨[⟨.or, [6, 5]⟩, ⟨.or, [8, 2]⟩, ⟨.or, [9, 11]⟩, ⟨.and, [1, 7]⟩, ⟨.or, [12, 1]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [3, 14]⟩, ⟨.and, [16, 15]⟩, ⟨.or, [14, 0]⟩, ⟨.and, [10, 18]⟩, ⟨.or, [13, 17]⟩, ⟨.or, [20, 19]⟩], 21⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
