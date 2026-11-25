import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Search for one circuit and join it to its point-line dual with a single OR.
theorem PEqualNP.Outside.R_meta_1683_4
    (joinCopies : ∀ (n : ℕ) (r : Fin n → Fin n) (D : Circuit),
      Monotone2 D → NestedCover.ReadsBack n D →
      ∃ C : Circuit, Monotone2 C ∧ C.size ≤ D.size + D.size + 1 ∧
        ∀ x : Fin n → Bool, circuitFun n C x =
          (circuitFun n D (fun i => x (r i)) || circuitFun n D x))
    (seed : let offsets : Finset (Fin 13) := {0, 1, 3, 9}
      let I := fun p w : Fin 13 => ∃ d ∈ offsets, p = w + d
      let row := fun p w : Fin 13 => Fin.append (fun i => decide (i = p)) (fun i => decide (i = w))
      ∃ D : Circuit, Monotone2 D ∧ NestedCover.ReadsBack 26 D ∧ D.size ≤ 31 ∧
        (∀ p w, I p w → p ≤ -w → circuitFun 26 D (row p w) = true ∨ circuitFun 26 D (row (-w) (-p)) = true) ∧
        ∀ a b : Fin 13 → Bool, (∀ p w, a p = true → b w = true → ¬ I p w) →
          ((∃ w, ∀ p, a p = true → I p w) ∨ (∃ p, ∀ w, b w = true → I p w)) →
          circuitFun 26 D (Fin.append a b) = false) :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 63 ∧ (∀ p w : Fin 13, (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = w + dd) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w)) = true) ∧ (∀ P : Finset (Fin 13), (∀ v : Fin 13, v ∉ P → ∃ w2 : Fin 13, (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w2 + dd)) ∧ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v = w2 + dd)) → ((∃ w3 : Fin 13, ∀ p3 ∈ P, (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p3 = w3 + dd)) ∨ (∃ v4 : Fin 13, ∀ w4 : Fin 13, (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w4 + dd)) → (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v4 = w4 + dd))) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun kk : Fin (13 + 13) => decide ((∃ pp ∈ P, kk = Fin.castAdd 13 pp) ∨ (∃ ww : Fin 13, kk = Fin.natAdd 13 ww ∧ (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = ww + dd))))) = false) := by
  let I := fun p w : Fin 13 => ∃ d ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = w + d
  let row := fun p w : Fin 13 => Fin.append (fun i => decide (i = p)) (fun i => decide (i = w))
  let r : Fin 26 → Fin 26 := Fin.append (fun p => Fin.natAdd 13 (-p)) (fun w => Fin.castAdd 13 (-w))
  have dual (p w : Fin 13) : I p w ↔ I (-w) (-p) := by
    revert p w
    decide +kernel
  have swapRow (p w : Fin 13) : (fun i => row p w (r i)) = row (-w) (-p) := by
    funext i
    revert p w i
    decide +kernel
  have rowEq (p w : Fin 13) : (fun k : Fin 26 => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w)) = row p w := by
    funext i
    revert p w i
    decide +kernel
  obtain ⟨D, hm, hr, hs, pos, neg⟩ := seed
  obtain ⟨C, hmC, hsC, evalC⟩ := joinCopies 26 r D hm hr
  refine ⟨C, hmC, by omega, ?_, ?_⟩
  · intro p w h
    rw [rowEq, evalC, swapRow, Bool.or_eq_true]
    by_cases order : p ≤ -w
    · exact (pos p w h order).symm
    · have rep : -w ≤ -(-p) := by simpa using le_of_not_ge order
      simpa only [neg_neg] using pos (-w) (-p) ((dual p w).mp h) rep
  · intro P _ degen
    let a := fun p : Fin 13 => decide (p ∈ P)
    let b := fun w : Fin 13 => decide (∀ p ∈ P, ¬ I p w)
    have disj (p w : Fin 13) (hp : a p = true) (hw : b w = true) : ¬ I p w :=
      of_decide_eq_true hw p (of_decide_eq_true hp)
    have cover : (∃ w, ∀ p, a p = true → I p w) ∨ (∃ p, ∀ w, b w = true → I p w) := by
      rcases degen with ⟨w, h⟩ | ⟨p, h⟩
      · exact Or.inl ⟨w, fun v hv => h v (of_decide_eq_true hv)⟩
      · exact Or.inr ⟨p, fun v hv => h v (of_decide_eq_true hv)⟩
    let x : Fin 26 → Bool := Fin.append a b
    have cross (p w : Fin 13) : Fin.castAdd 13 p ≠ Fin.natAdd 13 w := by
      revert p w
      decide +kernel
    have leftInj (i j : Fin 13) : Fin.castAdd 13 i = Fin.castAdd 13 j ↔ i = j := Fin.castAdd_inj
    have rightInj (i j : Fin 13) : Fin.natAdd 13 i = Fin.natAdd 13 j ↔ i = j := Fin.natAdd_inj 13
    have eqX : (fun k : Fin 26 => decide ((∃ p ∈ P, k = Fin.castAdd 13 p) ∨
        ∃ w : Fin 13, k = Fin.natAdd 13 w ∧ ∀ p ∈ P, ¬ I p w)) = x := by
      funext k
      refine Fin.addCases (m := 13) (n := 13) (fun p => ?_) (fun w => ?_) k
      · simp only [x, a, Fin.append_left, cross, false_and, exists_false, or_false, leftInj]
        congr 1
        apply propext
        constructor
        · rintro ⟨j, hj, rfl⟩
          exact hj
        · exact fun h => ⟨p, h, rfl⟩
      · simp only [x, b, Fin.append_right, fun w p => (cross p w).symm, and_false, exists_false,
          false_or, rightInj, exists_eq_left']
    have sx : (fun i => x (r i)) = Fin.append (fun p => b (-p)) (fun w => a (-w)) := by
      funext i
      refine Fin.addCases (m := 13) (n := 13) (fun p => ?_) (fun w => ?_) i <;> simp only [x, r, Fin.append_left, Fin.append_right]
    have sd (p w : Fin 13) (hp : b (-p) = true) (hw : a (-w) = true) : ¬ I p w :=
      fun h => disj (-w) (-p) hw hp ((dual p w).mp h)
    have sc : (∃ w : Fin 13, ∀ p, b (-p) = true → I p w) ∨
        (∃ p : Fin 13, ∀ w, a (-w) = true → I p w) := by
      rcases cover with ⟨w, h⟩ | ⟨p, h⟩
      · exact Or.inr ⟨-w, fun v hv => by simpa using (dual (-v) w).mp (h (-v) hv)⟩
      · exact Or.inl ⟨-p, fun v hv => by simpa using (dual p (-v)).mp (h (-v) hv)⟩
    rw [eqX, evalC, sx, neg _ _ sd sc, neg _ _ disj cover]
    rfl
