import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54606 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (3996924 : ℕ).testBit (6 * u.val + v.val)) 12 := by
  refine ⟨⟨[⟨.or, [4, 5]⟩, ⟨.or, [8, 2]⟩, ⟨.or, [7, 6]⟩, ⟨.or, [12, 1]⟩, ⟨.or, [10, 0]⟩, ⟨.or, [3, 11]⟩, ⟨.or, [15, 9]⟩, ⟨.and, [14, 13]⟩, ⟨.or, [10, 13]⟩, ⟨.or, [18, 0]⟩, ⟨.or, [16, 17]⟩, ⟨.and, [19, 20]⟩], 21⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
