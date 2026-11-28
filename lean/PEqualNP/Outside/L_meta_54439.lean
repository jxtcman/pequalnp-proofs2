import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54439 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (321015 : ℕ).testBit (6 * u.val + v.val)) 12 := by
  refine ⟨⟨[⟨.or, [6, 5]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [4, 2]⟩, ⟨.or, [7, 1]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [12, 14]⟩, ⟨.or, [3, 10]⟩, ⟨.and, [16, 12]⟩, ⟨.or, [0, 13]⟩, ⟨.and, [18, 15]⟩, ⟨.or, [17, 19]⟩, ⟨.or, [20, 11]⟩], 21⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
