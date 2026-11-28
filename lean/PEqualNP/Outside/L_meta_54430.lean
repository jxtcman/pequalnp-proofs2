import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54430 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (320502 : ℕ).testBit (6 * u.val + v.val)) 12 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.and, [7, 10]⟩, ⟨.or, [3, 8]⟩, ⟨.or, [9, 12]⟩, ⟨.or, [6, 5]⟩, ⟨.or, [1, 13]⟩, ⟨.or, [15, 14]⟩, ⟨.or, [4, 0]⟩, ⟨.and, [10, 14]⟩, ⟨.and, [17, 16]⟩, ⟨.or, [19, 11]⟩, ⟨.or, [18, 20]⟩], 21⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
