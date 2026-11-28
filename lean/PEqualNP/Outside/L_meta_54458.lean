import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54458 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (800573 : ℕ).testBit (6 * u.val + v.val)) 12 := by
  refine ⟨⟨[⟨.and, [0, 9]⟩, ⟨.or, [10, 4]⟩, ⟨.or, [6, 2]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [3, 7]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [8, 14]⟩, ⟨.and, [11, 0]⟩, ⟨.or, [17, 12]⟩, ⟨.or, [15, 13]⟩, ⟨.or, [16, 18]⟩, ⟨.and, [20, 19]⟩], 21⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
