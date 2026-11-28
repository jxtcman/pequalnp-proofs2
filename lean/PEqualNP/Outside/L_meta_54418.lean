import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54418 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (292605 : ℕ).testBit (6 * u.val + v.val)) 11 := by
  refine ⟨⟨[⟨.or, [6, 1]⟩, ⟨.or, [2, 8]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [11, 7]⟩, ⟨.and, [13, 9]⟩, ⟨.or, [13, 12]⟩, ⟨.and, [10, 13]⟩, ⟨.or, [5, 0]⟩, ⟨.or, [4, 16]⟩, ⟨.and, [15, 17]⟩, ⟨.or, [19, 18]⟩], 20⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
