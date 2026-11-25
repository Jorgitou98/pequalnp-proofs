import Mathlib.Data.Finset.Dedup
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.List.FinRange

-- A single list of gate instructions works simultaneously on all rows.
-- Each instruction contains an operation (true for union) and two wire indices.
-- The final two wires are incomparable exactly when both asymmetric rows exist.
theorem PEqualNP.Outside.R_meta_4955_1
    (compile : ∀ (n cap : ℕ) (inputs trace : List (Finset (Fin n))),
      inputs.length + trace.length ≤ cap →
      (∀ i : Fin trace.length, let prev := inputs ++ trace.take i.val;
        ∃ a ∈ prev, ∃ b ∈ prev, trace.get i = a ∩ b ∨ trace.get i = a ∪ b) →
      ∃ gs : List (Bool × Fin cap × Fin cap), gs.length = trace.length ∧
        ∀ r : Fin n,
          gs.foldl (fun (w : List Bool) g => w ++ [
            cond g.1 (w.getD g.2.1 false || w.getD g.2.2 false)
              (w.getD g.2.1 false && w.getD g.2.2 false)])
            (inputs.map fun s => decide (r ∈ s)) =
            (inputs ++ trace).map fun s => decide (r ∈ s))
    (separate :
      let seeds : List ℕ := [8193, 8194, 8200, 8704, 21233693, 3211303, 7340103, 23068749, 5275731, 22020181, 19923045, 18890857, 6357127, 6553741, 6324419, 6308041, 4751635, 21496089, 17318185, 20988233, 21004625, 17891877]
      ∀ gs : List (Bool × Fin 87 × Fin 87), gs.length ≤ 61 →
        let eval := fun (r : Fin 285) (j : ℕ) =>
          (gs.foldl (fun (w : List Bool) g => w ++ [
            cond g.1 (w.getD g.2.1 false || w.getD g.2.2 false)
              (w.getD g.2.1 false && w.getD g.2.2 false)])
            ((List.range 26).map fun v =>
              (seeds.getD ((r.val + 1) / 13) 0).testBit
                (v / 13 * 13 + (v + 13 - (r.val + 1) % 13) % 13))).getD j false
        ∀ a b : Fin 87, (∃ r, eval r a = true ∧ eval r b = false) →
          (∃ r, eval r b = true ∧ eval r a = false) →
          ∃ r, (eval r a && eval r b) ≠ decide (r.val < 51)) :
    have x1 : List ℕ := [(8193 : ℕ), (8194 : ℕ), (8200 : ℕ), (8704 : ℕ), (21233693 : ℕ), (3211303 : ℕ), (7340103 : ℕ), (23068749 : ℕ), (5275731 : ℕ), (22020181 : ℕ), (19923045 : ℕ), (18890857 : ℕ), (6357127 : ℕ), (6553741 : ℕ), (6324419 : ℕ), (6308041 : ℕ), (4751635 : ℕ), (21496089 : ℕ), (17318185 : ℕ), (20988233 : ℕ), (21004625 : ℕ), (17891877 : ℕ)];
    have x2 : List (Finset (Fin (285 : ℕ))) := List.map (fun (x2 : ℕ) =>
      (List.filter (fun (x3 : Fin (285 : ℕ)) => (x1.getD ((↑x3 + (1 : ℕ)) / (13 : ℕ)) (0 : ℕ)).testBit (x2 / (13 : ℕ) * (13 : ℕ) + (x2 + (13 : ℕ) - (↑x3 + (1 : ℕ)) % (13 : ℕ)) % (13 : ℕ))) (List.finRange (285 : ℕ))).toFinset) (List.range (26 : ℕ));
    ∀ (x3 : List (Finset (Fin (285 : ℕ)))),   x3.length ≤ (61 : ℕ) →
      (∀ (x5 : Fin x3.length),         have x6 : List (Finset (Fin (285 : ℕ))) := x2 ++ List.take (↑x5) x3;
         ∃ x7 ∈ x6, ∃ x8 ∈ x6, ¬x7 ⊆ x8 ∧ ¬x8 ⊆ x7 ∧ x3.get x5 ∉ x6 ∧ (x3.get x5 = x7 ∩ x8 ∨ x3.get x5 = x7 ∪ x8)) →
        ∀ x6 ∈ x2 ++ x3, ∀ x8 ∈ x2 ++ x3, ¬x6 ⊆ x8 → ¬x8 ⊆ x6 → x6 ∩ x8 ≠ (List.filter (fun (x12 : Fin (285 : ℕ)) => Decidable.decide (↑x12 < (51 : ℕ))) (List.finRange (285 : ℕ))).toFinset := by
  intro seeds inputs trace hlen valid a ha b hb hab hba meet
  let bit := fun (r : Fin 285) (v : ℕ) => (seeds.getD ((r.val + 1) / 13) 0).testBit
    (v / 13 * 13 + (v + 13 - (r.val + 1) % 13) % 13)
  have room : inputs.length + trace.length ≤ 87 := by
    have count : inputs.length = 26 := by simp [inputs]
    omega
  obtain ⟨gs, hgs, rows⟩ := compile 285 87 inputs trace room (by
    intro i
    obtain ⟨x, hx, y, hy, _, _, _, hop⟩ := valid i
    exact ⟨x, hx, y, hy, hop⟩)
  let eval := fun (r : Fin 285) (j : ℕ) =>
    (gs.foldl (fun (w : List Bool) g => w ++ [
      cond g.1 (w.getD g.2.1 false || w.getD g.2.2 false)
        (w.getD g.2.1 false && w.getD g.2.2 false)])
      ((List.range 26).map (bit r))).getD j false
  have init (r : Fin 285) : inputs.map (fun s => decide (r ∈ s)) = (List.range 26).map (bit r) := by
    simp [inputs, bit, List.map_map, Function.comp_def]
  obtain ⟨ia, hia, ea⟩ := List.getElem_of_mem ha
  obtain ⟨ib, hib, eb⟩ := List.getElem_of_mem hb
  have readAt (r : Fin 285) (i : ℕ) (hi : i < (inputs ++ trace).length) :
      eval r i = decide (r ∈ (inputs ++ trace)[i]) := by
    dsimp only [eval]
    rw [← init r, rows r]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi, Option.map_some, Option.getD_some]
  have ra (r : Fin 285) : eval r ia = decide (r ∈ a) := by rw [readAt r ia hia, ea]
  have rb (r : Fin 285) : eval r ib = decide (r ∈ b) := by rw [readAt r ib hib, eb]
  obtain ⟨u, hua, hub⟩ := Finset.not_subset.mp hab
  obtain ⟨v, hvb, hva⟩ := Finset.not_subset.mp hba
  have left : ∃ r, eval r ia = true ∧ eval r ib = false :=
    ⟨u, by simp [ra, hua], by simp [rb, hub]⟩
  have right : ∃ r, eval r ib = true ∧ eval r ia = false :=
    ⟨v, by simp [rb, hvb], by simp [ra, hva]⟩
  rw [List.length_append] at hia hib
  obtain ⟨r, bad⟩ := separate gs (hgs ▸ hlen) ⟨ia, by omega⟩ ⟨ib, by omega⟩ left right
  change (eval r ia && eval r ib) ≠ decide (r.val < 51) at bad
  apply bad
  rw [ra, rb, ← Bool.decide_and]
  congr 1
  apply propext
  rw [← Finset.mem_inter, meet]
  simp
