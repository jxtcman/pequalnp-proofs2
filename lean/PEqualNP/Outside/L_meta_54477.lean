import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54477 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (807864 : ℕ).testBit (6 * u.val + v.val)) 12 := by
  refine ⟨⟨[⟨.or, [5, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.or, [9, 8]⟩, ⟨.or, [4, 1]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [14, 7]⟩, ⟨.or, [12, 7]⟩, ⟨.and, [11, 10]⟩, ⟨.and, [0, 16]⟩, ⟨.and, [15, 13]⟩, ⟨.or, [18, 17]⟩, ⟨.or, [19, 20]⟩], 21⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
