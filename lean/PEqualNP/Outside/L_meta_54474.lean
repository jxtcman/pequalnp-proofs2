import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54474 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (807858 : ℕ).testBit (6 * u.val + v.val)) 12 := by
  refine ⟨⟨[⟨.or, [3, 6]⟩, ⟨.or, [1, 4]⟩, ⟨.or, [11, 0]⟩, ⟨.or, [7, 10]⟩, ⟨.and, [11, 13]⟩, ⟨.or, [8, 9]⟩, ⟨.and, [0, 15]⟩, ⟨.or, [16, 2]⟩, ⟨.or, [12, 10]⟩, ⟨.or, [17, 5]⟩, ⟨.or, [14, 19]⟩, ⟨.and, [18, 20]⟩], 21⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
