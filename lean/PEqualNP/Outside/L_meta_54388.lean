import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54388 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (323006 : ℕ).testBit (6 * u.val + v.val)) 11 := by
  refine ⟨⟨[⟨.or, [5, 6]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [0, 1]⟩, ⟨.and, [4, 3]⟩, ⟨.or, [11, 8]⟩, ⟨.and, [14, 12]⟩, ⟨.or, [7, 10]⟩, ⟨.or, [2, 0]⟩, ⟨.and, [16, 17]⟩, ⟨.or, [15, 18]⟩, ⟨.or, [13, 19]⟩], 20⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
