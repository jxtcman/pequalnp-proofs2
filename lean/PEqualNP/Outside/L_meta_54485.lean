import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54485 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (808507 : ℕ).testBit (6 * u.val + v.val)) 12 := by
  refine ⟨⟨[⟨.or, [8, 7]⟩, ⟨.or, [2, 10]⟩, ⟨.or, [6, 4]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [3, 0]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [11, 15]⟩, ⟨.and, [15, 9]⟩, ⟨.or, [18, 16]⟩, ⟨.and, [14, 19]⟩, ⟨.or, [17, 20]⟩], 21⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
