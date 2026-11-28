import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54472 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (807676 : ℕ).testBit (6 * u.val + v.val)) 12 := by
  refine ⟨⟨[⟨.or, [6, 1]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [2, 7]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [11, 10]⟩, ⟨.or, [11, 5]⟩, ⟨.or, [3, 8]⟩, ⟨.or, [16, 13]⟩, ⟨.and, [17, 15]⟩, ⟨.and, [0, 11]⟩, ⟨.and, [12, 14]⟩, ⟨.or, [18, 20]⟩], 21⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
