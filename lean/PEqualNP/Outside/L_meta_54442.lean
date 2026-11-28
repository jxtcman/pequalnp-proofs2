import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54442 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (322812 : ℕ).testBit (6 * u.val + v.val)) 12 := by
  refine ⟨⟨[⟨.or, [2, 8]⟩, ⟨.or, [1, 7]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [5, 0]⟩, ⟨.or, [13, 4]⟩, ⟨.or, [11, 6]⟩, ⟨.and, [12, 13]⟩, ⟨.or, [12, 14]⟩, ⟨.and, [17, 15]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [16, 18]⟩, ⟨.or, [20, 19]⟩], 21⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
