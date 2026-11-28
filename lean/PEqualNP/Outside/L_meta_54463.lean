import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54463 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (807355 : ℕ).testBit (6 * u.val + v.val)) 12 := by
  refine ⟨⟨[⟨.or, [1, 4]⟩, ⟨.or, [6, 0]⟩, ⟨.or, [11, 3]⟩, ⟨.or, [9, 8]⟩, ⟨.or, [5, 2]⟩, ⟨.or, [7, 13]⟩, ⟨.or, [12, 10]⟩, ⟨.and, [11, 15]⟩, ⟨.and, [14, 16]⟩, ⟨.and, [10, 12]⟩, ⟨.or, [17, 19]⟩, ⟨.or, [20, 18]⟩], 21⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
