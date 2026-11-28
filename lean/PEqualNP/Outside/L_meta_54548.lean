import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54548 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1881589 : ℕ).testBit (6 * u.val + v.val)) 12 := by
  refine ⟨⟨[⟨.or, [8, 6]⟩, ⟨.or, [9, 1]⟩, ⟨.or, [0, 5]⟩, ⟨.or, [12, 6]⟩, ⟨.or, [1, 7]⟩, ⟨.or, [10, 2]⟩, ⟨.or, [14, 12]⟩, ⟨.or, [3, 11]⟩, ⟨.and, [15, 16]⟩, ⟨.and, [17, 13]⟩, ⟨.or, [4, 18]⟩, ⟨.or, [20, 19]⟩], 21⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
