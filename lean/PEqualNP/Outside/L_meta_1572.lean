import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1572

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]

def run (gs : List Gate) (w : List Bool) := gs.foldl step w

lemma run_len (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (step w g)).length = _
    rw [ih]
    simp [step]
    omega

lemma run_read (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < w.length) :
    (run gs w).getD j false = w.getD j false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (step w g)).getD j false = _
    rw [ih _ (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hj

def val (gs : List Gate) (w : ℕ) (x : Fin 13 → Bool) :=
  Circuit.eval ⟨gs, w⟩ (List.ofFn x)

lemma input_val (gs : List Gate) (x : Fin 13 → Bool) (i : Fin 13) :
    val gs i.val x = x i := by
  have hi : i.val < (List.ofFn x).length := by simp
  change (run gs (List.ofFn x)).getD i.val false = x i
  rw [run_read _ _ _ hi, List.getD_eq_getElem _ _ hi, List.getElem_ofFn]

lemma valid_wire {gs : List Gate} {w : ℕ} {x : Fin 13 → Bool} (h : val gs w x = true) :
    w < 13 + gs.length := by
  by_contra! hle
  change (run gs (List.ofFn x)).getD w false = true at h
  have hlen : (run gs (List.ofFn x)).length = 13 + gs.length := by
    rw [run_len, List.length_ofFn]
  rw [List.getD_eq_default _ _ (hlen ▸ hle)] at h
  contradiction

def good (gs : List Gate) : Prop :=
  ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2

def back (gs : List Gate) : Prop :=
  ∀ i : Fin gs.length, 1 ≤ (gs.get i).inputs.length ∧
    ∀ a ∈ (gs.get i).inputs, a < 13 + i.val

lemma gate_val (gs : List Gate) (hb : back gs) (i : Fin gs.length) (x : Fin 13 → Bool) :
    val gs (13 + i.val) x = (gs.get i).op.eval ((gs.get i).inputs.map fun j => val gs j x) := by
  let w := run (gs.take i.val) (List.ofFn x)
  have hw : w.length = 13 + i.val := by
    simp [w, run_len]
  have hsplit : gs = gs.take i.val ++ gs.get i :: gs.drop (i.val + 1) := by
    change gs = gs.take i.val ++ gs[i.val] :: gs.drop (i.val + 1)
    rw [← List.drop_eq_getElem_cons i.isLt, List.take_append_drop]
  have hrun : run gs (List.ofFn x) = run (gs.drop (i.val + 1)) (step w (gs.get i)) := by
    unfold run
    conv_lhs => rw [hsplit, List.foldl_append]
    rfl
  change (run gs (List.ofFn x)).getD (13 + i.val) false = _
  rw [hrun, run_read _ _ _ (by simp [step, hw])]
  rw [show (step w (gs.get i)).getD (13 + i.val) false =
      (gs.get i).op.eval ((gs.get i).inputs.map fun j => w.getD j false) by
    rw [← hw]
    simp [step]]
  congr 1
  apply List.map_congr_left
  intro j hj
  have hlt : j < w.length := by rw [hw]; exact (hb i).2 j hj
  have hlt' : j < (step w (gs.get i)).length := by simp [step]; omega
  change _ = (run gs (List.ofFn x)).getD j false
  rw [hrun, run_read _ _ j hlt']
  exact (List.getD_append _ _ _ _ hlt).symm

lemma rises (gs : List Gate) (hg : good gs) (hb : back gs) (x y : Fin 13 → Bool)
    (w : ℕ) (hx : val gs w x = true) (hy : val gs w y = false) :
    ∃ i : Fin 13, x i = true ∧ y i = false := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw : w < 13
    · let i : Fin 13 := ⟨w, hw⟩
      exact ⟨i, (input_val gs x i).symm ▸ hx, (input_val gs y i).symm ▸ hy⟩
    · have hv := valid_wire hx
      let i : Fin gs.length := ⟨w - 13, by omega⟩
      have he : w = 13 + i.val := by dsimp [i]; omega
      rw [he, gate_val gs hb i] at hx hy
      rcases (hg _ (List.get_mem gs i)).1 with ho | ho
      · simp only [ho, GateOp.eval, List.all_map, List.all_eq_true, List.all_eq_false,
          Function.comp_apply, id_eq] at hx hy
        obtain ⟨j, hj, hjf⟩ := hy
        exact ih j (he ▸ (hb i).2 j hj) (hx j hj) (by simpa using hjf)
      · simp only [ho, GateOp.eval, List.any_map, List.any_eq_true, List.any_eq_false,
          Function.comp_apply, id_eq] at hx hy
        obtain ⟨j, hj, hjt⟩ := hx
        exact ih j (he ▸ (hb i).2 j hj) hjt (by simpa using hy j hj)

def covered (gs : List Gate) (g w : ℕ) : Prop :=
  ∀ S : Set ℕ, g ∈ S → (∀ i : Fin gs.length, 13 + i.val ∈ S →
    (gs.get i).op = .or → ∀ a ∈ (gs.get i).inputs, a ∈ S) → w ∈ S

lemma find_atom (gs : List Gate) (hg : good gs) (hb : back gs) {x y z : Fin 13 → Bool}
    (hxyz : ∀ i, x i = true → y i = true ∨ z i = true)
    (g w : ℕ) (hc : covered gs g w)
    (hx : val gs w x = true) (hy : val gs w y = false) (hz : val gs w z = false) :
    ∃ Y, covered gs g Y ∧ (∃ i : Fin gs.length, Y = 13 + i.val ∧ (gs.get i).op = .and) ∧
      val gs Y x = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw : w < 13
    · let i : Fin 13 := ⟨w, hw⟩
      have hp := hxyz i ((input_val gs x i).symm ▸ hx)
      rw [← input_val gs y i, ← input_val gs z i, hy, hz] at hp
      simp at hp
    · have hbound := valid_wire hx
      let i : Fin gs.length := ⟨w - 13, by omega⟩
      have he : w = 13 + i.val := by dsimp [i]; omega
      rcases (hg _ (List.get_mem gs i)).1 with ho | ho
      · exact ⟨w, hc, ⟨i, he, ho⟩, hx⟩
      · rw [he, gate_val gs hb i] at hx hy hz
        simp only [ho, GateOp.eval, List.any_map, List.any_eq_true, List.any_eq_false,
          Function.comp_apply, id_eq] at hx hy hz
        obtain ⟨j, hj, hjt⟩ := hx
        have hjw : j < w := by rw [he]; exact (hb i).2 j hj
        exact ih j hjw (fun S hS hs => hs i (he ▸ hc S hS hs) ho j hj) hjt
          (by simpa using hy j hj) (by simpa using hz j hj)

def line (t : Fin 13) : Finset (Fin 13) := {t, t + 1, t + 3, t + 9}

lemma pencil0 : ∀ t ∈ ({4, 10, 12} : Finset (Fin 13)), (0 : Fin 13) ∈ line t ∧ 1 ∉ line t := by decide

lemma pencil1 : ∀ t ∈ ({1, 5, 11} : Finset (Fin 13)), (1 : Fin 13) ∈ line t ∧ 0 ∉ line t := by decide

def co (A : Finset (Fin 13)) (v : Fin 13) : Bool := decide (v ∉ A)

def test (a b p v : Fin 13) : Bool := decide (v = p ∨ (p ≠ a ∧ v = b))

lemma side (gs : List Gate) (g : ℕ) (hg : good gs) (hb : back gs)
    {A B : Finset (Fin 13)} {a b c : Fin 13}
    (haB : a ∉ B) (hbA : b ∉ A) (hc : A ∩ B = {c})
    (hA : val gs g (co A) = false) (hB : val gs g (co B) = false)
    (ht : 2 ≤ (A.filter fun p => val gs g (test a b p) = true).card) :
    ∃ Y, covered gs g Y ∧ (∃ i : Fin gs.length, Y = 13 + i.val ∧ (gs.get i).op = .and) ∧
      ∃ p ∈ A, p ≠ a ∧ p ≠ c ∧ val gs Y (test a b p) = true := by
  have no_a : ∀ p, val gs g (test a b p) = true → p ≠ a := by
    intro p hp he
    subst p
    obtain ⟨v, hv, hv'⟩ := rises gs hg hb _ _ g hp hB
    have he : v = a := by simpa [test] using hv
    subst v
    simp [co, haB] at hv'
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp (by omega :
    1 < (A.filter fun p => val gs g (test a b p) = true).card)
  have hchoose : ∃ p ∈ A, p ≠ c ∧ val gs g (test a b p) = true := by
    by_cases he : p = c
    · exact ⟨q, (Finset.mem_filter.mp hq).1, fun h => hpq (he.trans h.symm), (Finset.mem_filter.mp hq).2⟩
    · exact ⟨p, (Finset.mem_filter.mp hp).1, he, (Finset.mem_filter.mp hp).2⟩
  obtain ⟨r, hr, hrc, hrt⟩ := hchoose
  have hrB : r ∉ B := by
    intro hrB
    have hh := Finset.mem_inter.mpr ⟨hr, hrB⟩
    rw [hc, Finset.mem_singleton] at hh
    exact hrc hh
  have htest (v : Fin 13) (hv : test a b r v = true) : co A v = true ∨ co B v = true := by
    rcases of_decide_eq_true hv with he | ⟨_, he⟩
    · subst v; exact Or.inr (decide_eq_true hrB)
    · subst v; exact Or.inl (decide_eq_true hbA)
  obtain ⟨Y, hY, hgate, hval⟩ := find_atom gs hg hb htest g g (fun _ h _ => h) hrt hA hB
  exact ⟨Y, hY, hgate, r, hr, no_a r hrt, hrc, hval⟩

end PEqualNP.Outside.L_meta_1572

theorem PEqualNP.Outside.L_meta_1572 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (g : ℕ) (l m c : Fin 13),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ)) → l ∈ ({4, 10, 12} : Finset (Fin 13)) → m ∈ ({1, 5, 11} : Finset (Fin 13)) → L l ∩ L m = {c} →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false →
    (2 ≤ ((L l).filter (fun p => PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 0 ∧ v = 1)))) = true)).card →
      ∃ Y : ℕ, (∀ S : Set ℕ, g ∈ S → (∀ i : Fin gates.length, 13 + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → Y ∈ S) ∧ (∃ i : Fin gates.length, Y = 13 + (i : ℕ) ∧ (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧ ∃ p ∈ L l, p ≠ 0 ∧ p ≠ c ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 0 ∧ v = 1)))) = true) ∧
    (2 ≤ ((L m).filter (fun p => PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 1 ∧ v = 0)))) = true)).card →
      ∃ Y : ℕ, (∀ S : Set ℕ, g ∈ S → (∀ i : Fin gates.length, 13 + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → Y ∈ S) ∧ (∃ i : Fin gates.length, Y = 13 + (i : ℕ) ∧ (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧ ∃ p ∈ L m, p ≠ 1 ∧ p ≠ c ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 1 ∧ v = 0)))) = true) := by
  intro L hL gs g l m c hg hb hl hm hc hv hv'
  have h0 : (0 : Fin 13) ∉ L m := by
    rw [hL m]
    exact (PEqualNP.Outside.L_meta_1572.pencil1 m hm).2
  have h1 : (1 : Fin 13) ∉ L l := by
    rw [hL l]
    exact (PEqualNP.Outside.L_meta_1572.pencil0 l hl).2
  exact ⟨PEqualNP.Outside.L_meta_1572.side gs g hg hb h0 h1 hc hv hv',
    PEqualNP.Outside.L_meta_1572.side gs g hg hb h1 h0 ((Finset.inter_comm _ _).trans hc) hv' hv⟩
