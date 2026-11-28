import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_53632 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1883964 : ℕ).testBit (6 * u.val + v.val)) 11 := by
  refine ⟨⟨[⟨.or, [6, 2]⟩, ⟨.or, [3, 7]⟩, ⟨.and, [11, 10]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [9, 8]⟩, ⟨.or, [14, 10]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [16, 5]⟩, ⟨.or, [1, 17]⟩, ⟨.or, [15, 11]⟩, ⟨.and, [18, 19]⟩], 20⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
