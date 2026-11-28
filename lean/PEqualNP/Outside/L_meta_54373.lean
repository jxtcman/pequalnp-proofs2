import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54373 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (294526 : ℕ).testBit (6 * u.val + v.val)) 11 := by
  refine ⟨⟨[⟨.or, [5, 1]⟩, ⟨.or, [6, 10]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [3, 11]⟩, ⟨.or, [12, 11]⟩, ⟨.and, [12, 13]⟩, ⟨.or, [15, 2]⟩, ⟨.or, [8, 16]⟩, ⟨.or, [7, 9]⟩, ⟨.or, [17, 18]⟩, ⟨.and, [14, 19]⟩], 20⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
