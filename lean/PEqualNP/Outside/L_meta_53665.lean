import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_53665 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (2072510 : ℕ).testBit (6 * u.val + v.val)) 11 := by
  refine ⟨⟨[⟨.or, [2, 6]⟩, ⟨.or, [8, 7]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [10, 5]⟩, ⟨.or, [4, 0]⟩, ⟨.or, [1, 14]⟩, ⟨.or, [12, 3]⟩, ⟨.and, [16, 13]⟩, ⟨.or, [13, 16]⟩, ⟨.or, [17, 15]⟩, ⟨.and, [19, 18]⟩], 20⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
