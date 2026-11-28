import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54437 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (321006 : ℕ).testBit (6 * u.val + v.val)) 12 := by
  refine ⟨⟨[⟨.or, [3, 7]⟩, ⟨.or, [6, 5]⟩, ⟨.or, [4, 0]⟩, ⟨.or, [10, 11]⟩, ⟨.and, [8, 9]⟩, ⟨.or, [1, 9]⟩, ⟨.or, [11, 8]⟩, ⟨.or, [16, 12]⟩, ⟨.or, [2, 12]⟩, ⟨.and, [17, 15]⟩, ⟨.and, [13, 18]⟩, ⟨.or, [20, 19]⟩], 21⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
