import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54387 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (322999 : ℕ).testBit (6 * u.val + v.val)) 11 := by
  refine ⟨⟨[⟨.or, [8, 9]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [3, 11]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [4, 2]⟩, ⟨.or, [12, 7]⟩, ⟨.or, [0, 1]⟩, ⟨.and, [13, 16]⟩, ⟨.or, [15, 0]⟩, ⟨.and, [14, 18]⟩, ⟨.or, [17, 19]⟩], 20⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
