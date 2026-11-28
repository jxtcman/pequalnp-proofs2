import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54496 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (810555 : ℕ).testBit (6 * u.val + v.val)) 12 := by
  refine ⟨⟨[⟨.or, [2, 9]⟩, ⟨.or, [7, 10]⟩, ⟨.or, [0, 3]⟩, ⟨.and, [12, 5]⟩, ⟨.or, [8, 11]⟩, ⟨.or, [4, 6]⟩, ⟨.or, [0, 15]⟩, ⟨.or, [16, 1]⟩, ⟨.and, [4, 12]⟩, ⟨.or, [13, 18]⟩, ⟨.and, [17, 14]⟩, ⟨.or, [19, 20]⟩], 21⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
