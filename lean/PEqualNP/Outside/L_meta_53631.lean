import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_53631 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1883253 : ℕ).testBit (6 * u.val + v.val)) 11 := by
  refine ⟨⟨[⟨.or, [0, 5]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 3]⟩, ⟨.or, [10, 1]⟩, ⟨.or, [6, 2]⟩, ⟨.or, [12, 9]⟩, ⟨.and, [13, 15]⟩, ⟨.or, [10, 11]⟩, ⟨.and, [17, 14]⟩, ⟨.or, [16, 4]⟩, ⟨.or, [18, 19]⟩], 20⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
