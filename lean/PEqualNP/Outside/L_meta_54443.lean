import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54443 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (322813 : ℕ).testBit (6 * u.val + v.val)) 12 := by
  refine ⟨⟨[⟨.or, [8, 2]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [11, 0]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [10, 4]⟩, ⟨.or, [13, 1]⟩, ⟨.or, [5, 12]⟩, ⟨.or, [14, 9]⟩, ⟨.and, [16, 15]⟩, ⟨.or, [16, 15]⟩, ⟨.and, [17, 19]⟩, ⟨.or, [20, 18]⟩], 21⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
