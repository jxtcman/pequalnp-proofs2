import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54379 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (321023 : ℕ).testBit (6 * u.val + v.val)) 10 := by
  refine ⟨⟨[⟨.or, [7, 3]⟩, ⟨.or, [4, 2]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [12, 8]⟩, ⟨.or, [12, 10]⟩, ⟨.or, [11, 13]⟩, ⟨.and, [1, 15]⟩, ⟨.and, [14, 11]⟩, ⟨.or, [17, 0]⟩, ⟨.or, [18, 16]⟩], 19⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
