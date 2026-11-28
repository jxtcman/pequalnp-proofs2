import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_53664 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (2072317 : ℕ).testBit (6 * u.val + v.val)) 11 := by
  refine ⟨⟨[⟨.or, [0, 5]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [6, 1]⟩, ⟨.and, [10, 12]⟩, ⟨.or, [11, 8]⟩, ⟨.or, [13, 14]⟩, ⟨.or, [12, 2]⟩, ⟨.or, [9, 15]⟩, ⟨.or, [16, 10]⟩, ⟨.and, [17, 18]⟩, ⟨.or, [19, 4]⟩], 20⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
