import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54391 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (324598 : ℕ).testBit (6 * u.val + v.val)) 11 := by
  refine ⟨⟨[⟨.or, [5, 6]⟩, ⟨.or, [10, 3]⟩, ⟨.or, [4, 0]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [2, 1]⟩, ⟨.or, [9, 14]⟩, ⟨.or, [8, 15]⟩, ⟨.or, [7, 13]⟩, ⟨.and, [11, 12]⟩, ⟨.and, [17, 16]⟩, ⟨.or, [19, 18]⟩], 20⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
