import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54389 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (323063 : ℕ).testBit (6 * u.val + v.val)) 11 := by
  refine ⟨⟨[⟨.or, [6, 5]⟩, ⟨.or, [4, 9]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [12, 1]⟩, ⟨.or, [11, 8]⟩, ⟨.or, [13, 0]⟩, ⟨.or, [10, 7]⟩, ⟨.and, [2, 16]⟩, ⟨.or, [10, 14]⟩, ⟨.and, [15, 18]⟩, ⟨.or, [19, 17]⟩], 20⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
