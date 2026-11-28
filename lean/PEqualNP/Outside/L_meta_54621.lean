import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54621 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (288445 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  refine ⟨⟨[⟨.or, [1, 6]⟩, ⟨.or, [8, 7]⟩, ⟨.or, [5, 0]⟩, ⟨.or, [11, 2]⟩, ⟨.or, [4, 9]⟩, ⟨.and, [13, 10]⟩, ⟨.or, [10, 14]⟩, ⟨.or, [15, 12]⟩, ⟨.or, [16, 13]⟩, ⟨.and, [17, 18]⟩, ⟨.and, [4, 3]⟩, ⟨.and, [18, 5]⟩, ⟨.or, [20, 19]⟩], 22⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
