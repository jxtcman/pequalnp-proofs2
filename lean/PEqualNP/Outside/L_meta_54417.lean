import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54417 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (292600 : ℕ).testBit (6 * u.val + v.val)) 12 := by
  refine ⟨⟨[⟨.or, [8, 7]⟩, ⟨.or, [6, 1]⟩, ⟨.or, [2, 10]⟩, ⟨.or, [9, 12]⟩, ⟨.or, [5, 4]⟩, ⟨.and, [12, 11]⟩, ⟨.or, [0, 15]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [1, 13]⟩, ⟨.or, [14, 16]⟩, ⟨.and, [18, 19]⟩, ⟨.or, [20, 17]⟩], 21⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
