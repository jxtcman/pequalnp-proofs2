import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54396 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (325566 : ℕ).testBit (6 * u.val + v.val)) 11 := by
  refine ⟨⟨[⟨.or, [7, 6]⟩, ⟨.or, [4, 0]⟩, ⟨.or, [10, 5]⟩, ⟨.or, [12, 11]⟩, ⟨.or, [8, 3]⟩, ⟨.or, [2, 9]⟩, ⟨.or, [1, 11]⟩, ⟨.and, [13, 15]⟩, ⟨.or, [12, 14]⟩, ⟨.and, [18, 16]⟩, ⟨.or, [17, 19]⟩], 20⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
