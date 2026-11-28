import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54364 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (292538 : ℕ).testBit (6 * u.val + v.val)) 11 := by
  refine ⟨⟨[⟨.or, [3, 5]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [4, 0]⟩, ⟨.or, [11, 10]⟩, ⟨.or, [12, 6]⟩, ⟨.or, [2, 9]⟩, ⟨.or, [1, 12]⟩, ⟨.or, [14, 5]⟩, ⟨.and, [17, 15]⟩, ⟨.and, [13, 16]⟩, ⟨.or, [19, 18]⟩], 20⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
