module

public import Certificates.Kernel.He27143.Checks
public import Certificates.Kernel.HeOrb.Final
import CFSG.Certificates.Kernel.Spor.VOrbSound
import CFSG.Certificates.Kernel.Spor.PackFld
import CFSG.Certificates.Kernel.Spor.TabWords

public section

namespace CFSG.KD.HeTab

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KC.HeTab CFSG.KD.HeOrb
  CFSG.EvenSporadicStandard.Induction CFSG.Sporadic.He.Native CFSG.Sporadic.Th.Native

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem allN_iff {n : Nat} {f : Nat → Bool} : allN n f = true ↔ ∀ i < n, f i = true :=
  ⟨allN_spec, CFSG.KS.PackFld.allN_of_forall⟩

theorem allIn_iff {n : Nat} {p : Nat → Bool} : allIn 0 n p = true ↔ ∀ i < n, p i = true :=
  CFSG.KS.TW.allIn_iff

theorem orb_facts {x : Nat} (hx : x < 8330) : r32 AL x < 8330 ∧ r32 BE x < 8330 :=
  ⟨(pt_facts hx).1, (pt_facts hx).2.1⟩

theorem inv_facts {x : Nat} (hx : x < 8330) : r32 BI x < 8330 ∧ r32 BI (r32 BE x) = x := by
  have h := allN_spec inv_ok x hx
  unfold invBK at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  exact ⟨Nat.blt_eq.mp h1, Nat.eq_of_beq_eq_true h2⟩

theorem invB : ∀ y < 8330, ap (invT 8330 OJ.beta) y = r32 BI y :=
  (CFSG.KS.VO.invT_get (f := r32 BE) (by norm_num) fun x hx =>
    ⟨beta_ap hx, (orb_facts hx).2, (inv_facts hx).2⟩).2

theorem GK_eq (z : Int) (x : Nat) : GK AL BE BI z x =
    if z = 1 ∨ z = -1 then r32 AL x else if z = 2 then r32 BE x else r32 BI x := by
  rcases z with ((_ | _ | _ | k) | (_ | k)) <;> rfl

theorem gens_get (z : Int) {x : Nat} (hx : x < 8330) :
    ap (genTables OJ z) x = GK AL BE BI z x ∧ GK AL BE BI z x < 8330 := by
  rw [GK_eq]
  have e : genTables OJ z = if z = 1 ∨ z = -1 then OJ.alpha else if z = 2 then OJ.beta
      else invT 8330 OJ.beta := rfl
  rw [e]
  split_ifs
  · exact ⟨alpha_ap hx, (orb_facts hx).1⟩
  · exact ⟨beta_ap hx, (orb_facts hx).2⟩
  · exact ⟨invB x hx, (inv_facts hx).1⟩

theorem word_get (k : Nat) (hk : k < 3) : ∀ x < 8330,
    ap (wordT 8330 (genTables OJ) (wSel k).2) x = r32 (wSel k).1 x ∧ r32 (wSel k).1 x < 8330 := by
  obtain ⟨-, hw⟩ := CFSG.KS.VO.wordT_ap (n := 8330) (by norm_num)
    (fun z y hy => gens_get z hy) (wSel k).2
  intro x hx
  obtain ⟨h1, h2⟩ := hw x hx
  have hc : 9 * k + x / 1000 < 27 := by omega
  have h := W.all (9 * k + x / 1000) hc
  unfold famW at h
  rw [strictB_eq, strictB_eq] at h
  have e1 : Nat.div (9 * k + x / 1000) 9 = k := by
    change (9 * k + x / 1000) / 9 = k
    omega
  have e2 : Nat.mul 1000 (Nat.mod (9 * k + x / 1000) 9) = 1000 * (x / 1000) := by
    change 1000 * ((9 * k + x / 1000) % 9) = _
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  rw [e1, e2] at h
  have h3 := allN_spec h (x % 1000) (Nat.mod_lt _ (by norm_num))
  rw [strictB_eq] at h3
  have ei : Nat.add (1000 * (x / 1000)) (x % 1000) = x := Nat.div_add_mod x 1000
  rw [ei] at h3
  have hx' : Nat.blt x (nat_lit 8330) = true := by rw [Nat.blt_eq]; exact hx
  have h4 := Nat.eq_of_beq_eq_true (CFSG.KS.HeVO.bIf_of h3 hx')
  rw [h1, ← h4]
  exact ⟨rfl, h4 ▸ h2⟩

theorem compT_ap {P Q : Table} {x : Nat} (hx : x < 8330) (hP : P.size = 8330)
    (hQ : ap Q x < 8330) : ap (compT 8330 P Q) x = ap P (ap Q x) := by
  unfold compT ap
  rw [getElem!_pos _ x (by simpa using hx), Array.getElem_ofFn]

theorem idT_ap {x : Nat} (hx : x < 8330) : ap (idT 8330) x = x := by
  unfold idT ap
  rw [getElem!_pos _ x (by simpa using hx), Array.getElem_ofFn, UInt32.toNat_ofNat']
  exact Nat.mod_eq_of_lt (by omega)

theorem eqTab_iff {T T' : Table} : eqTab 8330 T T' = true ↔ ∀ i < 8330, ap T i = ap T' i := by
  unfold eqTab
  rw [allIn_iff]
  simp only [beq_iff_eq]

theorem movesK_iff {f g : Nat → Nat} : movesK f g = true ↔ ¬ ∀ x < 8330, f x = g x := by
  unfold movesK
  cases h : allN (nat_lit 8330) fun x => Nat.beq (f x) (g x)
  · refine ⟨fun _ h' => ?_, fun _ => rfl⟩
    have : allN (nat_lit 8330) (fun x => Nat.beq (f x) (g x)) = true :=
      allN_iff.2 fun x hx => Nat.beq_eq_true_eq _ _ ▸ h' x hx
    rw [h] at this
    exact absurd this (by decide)
  · refine ⟨fun e => absurd e (by decide), fun hn => absurd (fun x hx => ?_) hn⟩
    exact Nat.eq_of_beq_eq_true (allN_spec h x hx)

theorem heE8_ok : heE8Check (orbitData ()) = true := by
  rw [orbitData_eq]
  have hX := word_get 0 (by norm_num)
  have hY := word_get 1 (by norm_num)
  have hZ := word_get 2 (by norm_num)
  have e0 : wSel 0 = (WX, heWordE1) := rfl
  have e1 : wSel 1 = (WY, heWordE2) := rfl
  have e2 : wSel 2 = (WZ, heWordE3) := rfl
  rw [e0] at hX
  rw [e1] at hY
  rw [e2] at hZ
  simp only at hX hY hZ
  have sz : ∀ w, (wordT 8330 (genTables OJ) w).size = 8330 := fun w =>
    (CFSG.KS.VO.wordT_ap (n := 8330) (by norm_num) (fun z y hy => gens_get z hy) w).1
  have hne := ne_ok
  simp only [Bool.and_eq_true, movesK_iff] at hne
  obtain ⟨⟨⟨⟨⟨⟨n1, n2⟩, n3⟩, n4⟩, n5⟩, n6⟩, n7⟩ := hne
  have cmp : ∀ {A B : Table} {fa fb : Nat → Nat}, A.size = 8330 →
      (∀ x < 8330, ap A x = fa x ∧ fa x < 8330) → (∀ x < 8330, ap B x = fb x ∧ fb x < 8330) →
      ∀ x < 8330, ap (compT 8330 A B) x = fa (fb x) := by
    intro A B fa fb hA ha hb x hx
    rw [compT_ap hx hA (by rw [(hb x hx).1]; exact (hb x hx).2), (hb x hx).1,
      (ha _ (hb x hx).2).1]
  have hI : ∀ x < 8330, ap (idT 8330) x = x := fun x hx => idT_ap hx
  have e8 : ∀ x < 8330, r32 WX (r32 WX x) = x ∧ r32 WY (r32 WY x) = x ∧
      r32 WZ (r32 WZ x) = x ∧ r32 WX (r32 WY x) = r32 WY (r32 WX x) ∧
      r32 WX (r32 WZ x) = r32 WZ (r32 WX x) ∧ r32 WY (r32 WZ x) = r32 WZ (r32 WY x) := by
    intro x hx
    have h := allN_spec e8_ok x hx
    unfold e8K at h
    obtain ⟨h1, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨h2, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨h3, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨h4, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨h5, h6⟩ := (bAnd_iff _ _).1 h
    exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3,
      Nat.eq_of_beq_eq_true h4, Nat.eq_of_beq_eq_true h5, Nat.eq_of_beq_eq_true h6⟩
  have ne : ∀ {T T' : Table} {f g : Nat → Nat}, (∀ x < 8330, ap T x = f x) →
      (∀ x < 8330, ap T' x = g x) → (¬ ∀ x < 8330, f x = g x) → eqTab 8330 T T' = false := by
    intro T T' f g hT hT' hn
    rw [Bool.eq_false_iff]
    intro h
    refine hn fun x hx => ?_
    rw [← hT x hx, ← hT' x hx]
    exact eqTab_iff.1 h x hx
  have hXY : ∀ x < 8330, ap (compT 8330 (wordT 8330 (genTables OJ) heWordE1)
      (wordT 8330 (genTables OJ) heWordE2)) x = r32 WX (r32 WY x) := cmp (sz _) hX hY
  unfold heE8Check
  simp only [Bool.and_eq_true, Bool.not_eq_true', eqTab_iff]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨fun x hx => ?_, fun x hx => ?_⟩, fun x hx => ?_⟩, fun x hx => ?_⟩,
    fun x hx => ?_⟩, fun x hx => ?_⟩, ne (fun x hx => (hX x hx).1) hI n1⟩,
    ne (fun x hx => (hY x hx).1) hI n2⟩, ne (fun x hx => (hY x hx).1) (fun x hx => (hX x hx).1) n3⟩,
    ne (fun x hx => (hZ x hx).1) hI n4⟩, ne (fun x hx => (hZ x hx).1) (fun x hx => (hX x hx).1) n5⟩,
    ne (fun x hx => (hZ x hx).1) (fun x hx => (hY x hx).1) n6⟩,
    ne (fun x hx => (hZ x hx).1) hXY n7⟩
  · rw [cmp (sz _) hX hX x hx, hI x hx, (e8 x hx).1]
  · rw [cmp (sz _) hY hY x hx, hI x hx, (e8 x hx).2.1]
  · rw [cmp (sz _) hZ hZ x hx, hI x hx, (e8 x hx).2.2.1]
  · rw [cmp (sz _) hX hY x hx, cmp (sz _) hY hX x hx, (e8 x hx).2.2.2.1]
  · rw [cmp (sz _) hX hZ x hx, cmp (sz _) hZ hX x hx, (e8 x hx).2.2.2.2.1]
  · rw [cmp (sz _) hY hZ x hx, cmp (sz _) hZ hY x hx, (e8 x hx).2.2.2.2.2]

end CFSG.KD.HeTab

end
