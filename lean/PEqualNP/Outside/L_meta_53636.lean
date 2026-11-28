import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_53636 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1897961 : ℕ).testBit (6 * u.val + v.val)) 11 := by
  refine ⟨⟨[⟨.or, [0, 6]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [10, 5]⟩, ⟨.or, [11, 9]⟩, ⟨.or, [7, 1]⟩, ⟨.or, [12, 8]⟩, ⟨.or, [15, 2]⟩, ⟨.and, [14, 16]⟩, ⟨.and, [13, 12]⟩, ⟨.or, [17, 18]⟩, ⟨.or, [4, 19]⟩], 20⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
