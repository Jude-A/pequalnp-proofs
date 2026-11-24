import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1632

open PEqualNP.CircuitLowerBounds

private lemma read_fold (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) w).getD
      i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp; omega)]
    exact List.getD_append _ _ _ _ hi

private lemma input_eval {N : ℕ} (gs : List Gate) (x : Fin N → Bool) (i : Fin N) :
    Circuit.eval ⟨gs, i.val⟩ (List.ofFn x) = x i := by
  have hi : i.val < (List.ofFn x).length := by simpa only [List.length_ofFn] using i.isLt
  unfold Circuit.eval Circuit.wires
  rw [read_fold _ _ _ hi, List.getD_eq_getElem _ _ hi, List.getElem_ofFn]

private lemma disjoint_off_center {N : ℕ} (L : Fin N → Finset (Fin N))
    (h : ∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) {i j c p : Fin N}
    (hne : i ≠ j) (hci : c ∈ L i) (hcj : c ∈ L j) (hpi : p ∈ L i) (hpc : p ≠ c) :
    p ∉ L j := by
  intro hpj
  have hsub : ({p, c} : Finset (Fin N)) ⊆ L i ∩ L j := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact Finset.mem_inter.mpr ⟨hpi, hpj⟩
    · exact Finset.mem_inter.mpr ⟨hci, hcj⟩
  have hcard := Finset.card_le_card hsub
  simp [Finset.card_pair hpc, h i j hne] at hcard

end PEqualNP.Outside.L_meta_1632

theorem PEqualNP.Outside.L_meta_1632 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    (∀ l l' : Fin N, (p0 ∈ L l ∧ p1 ∉ L l) → (p0 ∈ L l' ∧ p1 ∉ L l') → l ≠ l' → ∀ p ∈ L l, p ≠ p0 → p1 ∉ L l' ∧ p ∉ L l') ∧
    (∀ m m' : Fin N, (p1 ∈ L m ∧ p0 ∉ L m) → (p1 ∈ L m' ∧ p0 ∉ L m') → m ≠ m' → ∀ p ∈ L m, p ≠ p1 → p0 ∉ L m' ∧ p ∉ L m') ∧
    (∀ m : Fin N, (p1 ∈ L m ∧ p0 ∉ L m) → p0 ∉ L m) ∧ (∀ l : Fin N, (p0 ∈ L l ∧ p1 ∉ L l) → p1 ∉ L l) ∧
    (∀ M m : Fin N, (p0 ∉ L M ∧ p1 ∉ L M) → (p1 ∈ L m ∧ p0 ∉ L m) → ∀ p ∈ L M, p ∉ L m → p0 ∉ L m ∧ p ∉ L m) ∧
    (∀ l m : Fin N, (p0 ∈ L l ∧ p1 ∉ L l) → (p1 ∈ L m ∧ p0 ∉ L m) → ∃ c : Fin N, L l ∩ L m = {c}) ∧
    (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate), (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ gt.inputs.length ≤ 2) →
      (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length) → (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
      ∀ p t : Fin N, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, (p : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L t))) = false ↔ p ∈ L t) := by
  intro q N L i0 p0 p1 _ _ _ hInter _ _ _ _
  refine ⟨?_, ?_, fun _ h => h.2, fun _ h => h.2, fun _ _ _ h _ _ hp => ⟨h.2, hp⟩, ?_, ?_⟩
  · intro l l' hl hl' hne p hp hpc
    exact ⟨hl'.2, PEqualNP.Outside.L_meta_1632.disjoint_off_center L hInter hne hl.1 hl'.1 hp hpc⟩
  · intro m m' hm hm' hne p hp hpc
    exact ⟨hm'.2, PEqualNP.Outside.L_meta_1632.disjoint_off_center L hInter hne hm.1 hm'.1 hp hpc⟩
  · intro l m hl hm
    have hne : l ≠ m := fun he => hl.2 (he.symm ▸ hm.1)
    exact Finset.card_eq_one.mp (hInter l m hne)
  · intro gates _ _ _ p t
    rw [PEqualNP.Outside.L_meta_1632.input_eval]
    simp
