import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54361 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (291832 : ℕ).testBit (6 * u.val + v.val)) 11 := by
  refine ⟨⟨[⟨.or, [0, 4]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [8, 11]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [9, 12]⟩, ⟨.or, [10, 1]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [16, 15]⟩, ⟨.or, [13, 10]⟩, ⟨.and, [18, 14]⟩, ⟨.or, [17, 19]⟩], 20⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
