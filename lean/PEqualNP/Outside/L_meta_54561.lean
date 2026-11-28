import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54561 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1883447 : ℕ).testBit (6 * u.val + v.val)) 12 := by
  refine ⟨⟨[⟨.or, [7, 1]⟩, ⟨.or, [3, 0]⟩, ⟨.or, [5, 4]⟩, ⟨.or, [6, 9]⟩, ⟨.or, [12, 0]⟩, ⟨.or, [8, 13]⟩, ⟨.or, [2, 15]⟩, ⟨.or, [6, 12]⟩, ⟨.or, [14, 10]⟩, ⟨.and, [17, 11]⟩, ⟨.and, [18, 16]⟩, ⟨.or, [19, 20]⟩], 21⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
