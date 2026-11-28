import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54447 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (325551 : ℕ).testBit (6 * u.val + v.val)) 12 := by
  refine ⟨⟨[⟨.and, [0, 9]⟩, ⟨.or, [10, 6]⟩, ⟨.or, [2, 0]⟩, ⟨.or, [1, 4]⟩, ⟨.or, [7, 11]⟩, ⟨.or, [3, 5]⟩, ⟨.or, [14, 15]⟩, ⟨.or, [8, 16]⟩, ⟨.and, [12, 16]⟩, ⟨.or, [17, 12]⟩, ⟨.or, [18, 13]⟩, ⟨.and, [19, 20]⟩], 21⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
