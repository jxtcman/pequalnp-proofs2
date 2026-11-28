import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54501 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (851256 : ℕ).testBit (6 * u.val + v.val)) 12 := by
  refine ⟨⟨[⟨.or, [9, 2]⟩, ⟨.or, [10, 8]⟩, ⟨.or, [6, 0]⟩, ⟨.and, [12, 11]⟩, ⟨.or, [5, 4]⟩, ⟨.or, [3, 10]⟩, ⟨.and, [15, 14]⟩, ⟨.or, [13, 16]⟩, ⟨.or, [7, 1]⟩, ⟨.or, [12, 11]⟩, ⟨.and, [18, 19]⟩, ⟨.or, [17, 20]⟩], 21⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
