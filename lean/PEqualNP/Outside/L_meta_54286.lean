import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54286 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (807669 : ℕ).testBit (6 * u.val + v.val)) 10 := by
  refine ⟨⟨[⟨.or, [5, 0]⟩, ⟨.or, [6, 1]⟩, ⟨.or, [3, 9]⟩, ⟨.or, [7, 2]⟩, ⟨.and, [13, 11]⟩, ⟨.or, [8, 12]⟩, ⟨.or, [15, 11]⟩, ⟨.or, [4, 14]⟩, ⟨.and, [10, 16]⟩, ⟨.or, [17, 18]⟩], 19⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
