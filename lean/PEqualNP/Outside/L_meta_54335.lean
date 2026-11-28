import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54335 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (288382 : ℕ).testBit (6 * u.val + v.val)) 11 := by
  refine ⟨⟨[⟨.or, [8, 7]⟩, ⟨.or, [4, 0]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [10, 9]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [13, 3]⟩, ⟨.or, [12, 1]⟩, ⟨.or, [14, 2]⟩, ⟨.and, [16, 17]⟩, ⟨.and, [11, 15]⟩, ⟨.or, [18, 19]⟩], 20⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
