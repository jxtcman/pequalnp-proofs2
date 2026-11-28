import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54473 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (807857 : ℕ).testBit (6 * u.val + v.val)) 12 := by
  refine ⟨⟨[⟨.or, [6, 3]⟩, ⟨.or, [5, 2]⟩, ⟨.or, [9, 8]⟩, ⟨.and, [12, 0]⟩, ⟨.and, [10, 11]⟩, ⟨.or, [7, 10]⟩, ⟨.or, [11, 0]⟩, ⟨.or, [4, 14]⟩, ⟨.or, [1, 13]⟩, ⟨.or, [17, 18]⟩, ⟨.or, [16, 15]⟩, ⟨.and, [20, 19]⟩], 21⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
