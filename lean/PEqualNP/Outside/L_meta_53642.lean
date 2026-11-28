import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_53642 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1898235 : ℕ).testBit (6 * u.val + v.val)) 11 := by
  refine ⟨⟨[⟨.or, [4, 5]⟩, ⟨.or, [8, 3]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [12, 7]⟩, ⟨.or, [12, 1]⟩, ⟨.or, [7, 11]⟩, ⟨.or, [2, 9]⟩, ⟨.and, [15, 14]⟩, ⟨.and, [13, 16]⟩, ⟨.or, [17, 10]⟩, ⟨.or, [18, 19]⟩], 20⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
