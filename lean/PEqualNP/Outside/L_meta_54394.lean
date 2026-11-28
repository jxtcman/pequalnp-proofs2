import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54394 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (325113 : ℕ).testBit (6 * u.val + v.val)) 10 := by
  refine ⟨⟨[⟨.or, [2, 8]⟩, ⟨.or, [6, 0]⟩, ⟨.or, [7, 1]⟩, ⟨.and, [12, 10]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [4, 13]⟩, ⟨.or, [12, 14]⟩, ⟨.or, [11, 5]⟩, ⟨.and, [17, 16]⟩, ⟨.or, [15, 18]⟩], 19⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
