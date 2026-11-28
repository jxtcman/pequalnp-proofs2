import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54459 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (800622 : ℕ).testBit (6 * u.val + v.val)) 12 := by
  refine ⟨⟨[⟨.or, [6, 7]⟩, ⟨.or, [5, 1]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [11, 9]⟩, ⟨.or, [13, 8]⟩, ⟨.or, [15, 13]⟩, ⟨.and, [3, 14]⟩, ⟨.and, [16, 11]⟩, ⟨.and, [17, 14]⟩, ⟨.or, [19, 20]⟩], 21⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
