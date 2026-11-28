import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54495 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (808894 : ℕ).testBit (6 * u.val + v.val)) 12 := by
  refine ⟨⟨[⟨.or, [6, 3]⟩, ⟨.or, [5, 2]⟩, ⟨.or, [1, 4]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [13, 11]⟩, ⟨.and, [10, 11]⟩, ⟨.and, [9, 0]⟩, ⟨.or, [0, 12]⟩, ⟨.or, [14, 10]⟩, ⟨.and, [17, 18]⟩, ⟨.or, [15, 16]⟩, ⟨.or, [20, 19]⟩], 21⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
