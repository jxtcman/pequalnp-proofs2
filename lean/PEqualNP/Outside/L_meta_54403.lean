import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54403 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (291580 : ℕ).testBit (6 * u.val + v.val)) 12 := by
  refine ⟨⟨[⟨.or, [7, 2]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [6, 1]⟩, ⟨.or, [0, 4]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [11, 14]⟩, ⟨.and, [12, 10]⟩, ⟨.or, [13, 5]⟩, ⟨.or, [17, 16]⟩, ⟨.or, [15, 10]⟩, ⟨.or, [12, 19]⟩, ⟨.and, [18, 20]⟩], 21⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
