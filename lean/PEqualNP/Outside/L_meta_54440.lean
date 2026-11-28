import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54440 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (321459 : ℕ).testBit (6 * u.val + v.val)) 12 := by
  refine ⟨⟨[⟨.or, [3, 8]⟩, ⟨.or, [2, 9]⟩, ⟨.or, [1, 4]⟩, ⟨.or, [0, 12]⟩, ⟨.or, [0, 7]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [10, 5]⟩, ⟨.or, [11, 12]⟩, ⟨.and, [13, 16]⟩, ⟨.or, [14, 15]⟩, ⟨.and, [17, 19]⟩, ⟨.or, [18, 20]⟩], 21⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
