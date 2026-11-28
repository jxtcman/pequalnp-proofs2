import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54466 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (807606 : ℕ).testBit (6 * u.val + v.val)) 12 := by
  refine ⟨⟨[⟨.or, [9, 8]⟩, ⟨.or, [5, 2]⟩, ⟨.or, [3, 6]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [4, 0]⟩, ⟨.and, [13, 14]⟩, ⟨.or, [1, 14]⟩, ⟨.or, [15, 11]⟩, ⟨.and, [7, 1]⟩, ⟨.or, [12, 16]⟩, ⟨.or, [18, 17]⟩, ⟨.and, [20, 19]⟩], 21⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
