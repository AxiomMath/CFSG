module

public import Certificates.Kernel.SporSch.Pair.J2Fib
public import Certificates.Kernel.SporSch.Pair.J2FibData

public section

namespace CertificateChecks.KernelSporSch.PJ2Fib

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch
open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative CFSG.Sporadic.Schreier.PairJ2
open CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.PJ2Check
open CertificateChecks.KernelSporSch.PJ2W CertificateChecks.KernelSporSch.PJ2Orb

@[expose] noncomputable def spW : List Nat → Equiv.Perm (Fin 315)
  | [] => 1
  | j :: L => spW L * permOfArr 315 (j2StrongArrs ())[j]!

theorem spW_append (A C : List Nat) : spW (A ++ C) = spW C * spW A := by
  induction A with
  | nil => simp [spW]
  | cons j A ih => simp only [List.cons_append, spW, ih, mul_assoc]

theorem spW_mem : ∀ L : List Nat, (∀ j ∈ L, j < 7) → spW L ∈ j2Chain.originalSubgroup
  | [], _ => j2Chain.originalSubgroup.one_mem
  | j :: L, h => j2Chain.originalSubgroup.mul_mem
      (spW_mem L fun i hi => h i (List.mem_cons_of_mem _ hi)) (strong_mem j (h j List.mem_cons_self))

theorem spW_rep : ∀ L : List Nat, (∀ j ∈ L, j < 7) →
    RepW 315 ((L.map PJ2.S).map (unpack 315 9)) (spW L)
  | [], _ => repW_nil
  | j :: L, h => by
    have hj := h j List.mem_cons_self
    have h1 : RepW 315 [unpack 315 9 (PJ2.S j)] (permOfArr 315 (j2StrongArrs ())[j]!) := fun x =>
      (congrArg (fun t => evR [t] (x : Nat)) (PJ2.arr_eq j hj)).symm.trans (strong_rep j hj x)
    exact h1.append (spW_rep L fun i hi => h i (List.mem_cons_of_mem _ hi))

theorem rangeS (L : List Nat) (hL : ∀ j ∈ L, j < 7) : Cnt3P.RangeL 315 9 (L.map PJ2.S) := by
  intro W hW
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hW
  exact Cnt3P.rangeL_of_canonL canonS _ (List.mem_map.2 ⟨j, List.mem_range.2 (hL j hj), rfl⟩)

theorem range2 {A B : Nat} (hA : canonL 315 9 [A] = true) (hB : canonL 315 9 [B] = true) :
    Cnt3P.RangeL 315 9 [A, B] := by
  intro W hW
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hW
  rcases hW with rfl | rfl
  · exact Cnt3P.rangeL_of_canonL hA _ List.mem_cons_self
  · exact Cnt3P.rangeL_of_canonL hB _ List.mem_cons_self

theorem repW_ofK {Ws : List Nat} {X : Nat} (hW : Cnt3P.RangeL 315 9 Ws)
    (hX : canonL 315 9 [X] = true)
    (hag : allN 315 (fun p => Nat.beq (evRK 9 Ws p) (evRK 9 [X] p)) = true)
    {g : Equiv.Perm (Fin 315)} (hg : RepW 315 (Ws.map (unpack 315 9)) g) :
    RepW 315 ([X].map (unpack 315 9)) g := fun x => by
  rw [← hg x, ← (Cnt3P.evRK_eq hW x x.2).1, Nat.eq_of_beq_eq_true (allN_spec hag x x.2)]
  exact (Cnt3P.evRK_eq (Cnt3P.rangeL_of_canonL hX) x x.2).1.symm

theorem spW_inv {A C : List Nat} (hA : ∀ j ∈ A, j < 7) (hC : ∀ j ∈ C, j < 7)
    (hid : allN 315 (fun p => Nat.beq (evRK 9 ((A ++ C).map PJ2.S) p) p) = true) :
    spW C = (spW A)⁻¹ := by
  have hAC : ∀ j ∈ A ++ C, j < 7 := fun j hj => (List.mem_append.1 hj).elim (hA j) (hC j)
  have h1 : RepW 315 (((A ++ C).map PJ2.S).map (unpack 315 9)) 1 := fun x => by
    rw [← (Cnt3P.evRK_eq (rangeS _ hAC) x x.2).1, Nat.eq_of_beq_eq_true (allN_spec hid x x.2)]
    rfl
  have e := (spW_rep _ hAC).unique h1
  rw [spW_append] at e
  exact eq_inv_of_mul_eq_one_left e

theorem spW_conj {A M C : List Nat} (hA : ∀ j ∈ A, j < 7) (hC : ∀ j ∈ C, j < 7)
    (hid : allN 315 (fun p => Nat.beq (evRK 9 ((A ++ C).map PJ2.S) p) p) = true) :
    spW (A ++ M ++ C) = (spW A)⁻¹ * spW M * (spW A)⁻¹⁻¹ := by
  simp only [spW_append, spW_inv hA hC hid, inv_inv, mul_assoc]

theorem comm_ofK {X Y : Nat} (hX : canonL 315 9 [X] = true) (hY : canonL 315 9 [Y] = true)
    (hc : allN 315 (fun p => Nat.beq (evRK 9 [X, Y] p) (evRK 9 [Y, X] p)) = true)
    {gx gy : Equiv.Perm (Fin 315)} (hx : RepW 315 ([X].map (unpack 315 9)) gx)
    (hy : RepW 315 ([Y].map (unpack 315 9)) gy) : gx * gy * gx⁻¹ = gy := by
  have e : gy * gx = gx * gy := Equiv.ext fun x => Fin.ext <| by
    rw [← hx.append hy x, ← hy.append hx x]
    change evR ([X, Y].map (unpack 315 9)) x = evR ([Y, X].map (unpack 315 9)) x
    rw [← (Cnt3P.evRK_eq (range2 hX hY) x x.2).1, ← (Cnt3P.evRK_eq (range2 hY hX) x x.2).1]
    exact Nat.eq_of_beq_eq_true (allN_spec hc x x.2)
  rw [← e, mul_inv_cancel_right]

theorem hw_lt : ∀ i, ∀ j ∈ HW.getD i [], j < 7
  | 0 | 1 | 2 | 3 => by decide
  | _ + 4 => by simp [HW]

@[expose] noncomputable def hs (i : Nat) : Equiv.Perm (Fin 315) := spW (HW.getD i [])

theorem hs_ge {i : Nat} (hi : ¬i < 4) : hs i = 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_lt hi)
  simp [hs, HW, spW]

theorem hs_mem (i : Nat) : hs i ∈ j2Chain.originalSubgroup := spW_mem _ (hw_lt i)

theorem hs_rep {i : Nat} (hi : i < 4) : RepW 315 ([HL.getD i 0].map (unpack 315 9)) (hs i) :=
  repW_ofK (rangeS _ (hw_lt i)) (allN_spec canonH i hi) (allN_spec agH i hi) (spW_rep _ (hw_lt i))

theorem hs_one (i : Nat) : hs i 1 = 1 := by
  by_cases hi : i < 4
  · refine Fin.ext ?_
    have e1 : ((1 : Fin 315) : Nat) = 1 := rfl
    rw [← hs_rep hi 1, e1, ← (Cnt3P.evRK_eq (Cnt3P.rangeL_of_canonL (allN_spec canonH i hi)) 1 (by norm_num)).1]
    exact Nat.eq_of_beq_eq_true (allN_spec fixH i hi)
  · rw [hs_ge hi]
    rfl

@[expose] noncomputable def uG : Equiv.Perm (Fin 315) := spW (UA ++ UM ++ UC)

@[expose] noncomputable def zG : Equiv.Perm (Fin 315) := spW (ZA ++ ZM ++ ZC)

theorem uG_rep : RepW 315 ([U].map (unpack 315 9)) uG :=
  repW_ofK (rangeS _ (by decide)) canonU agU (spW_rep _ (by decide))

theorem zG_rep : RepW 315 ([Z].map (unpack 315 9)) zG :=
  repW_ofK (rangeS _ (by decide)) canonZ agZ (spW_rep _ (by decide))

theorem uG_mem : uG ∈ j2Chain.originalSubgroup := spW_mem _ (by decide)

theorem zG_mem : zG ∈ j2Chain.originalSubgroup := spW_mem _ (by decide)

theorem uG_conj : uG = (spW UA)⁻¹ * spW UM * (spW UA)⁻¹⁻¹ :=
  spW_conj (by decide) (by decide) idU

theorem zG_conj : zG = (spW ZA)⁻¹ * spW ZM * (spW ZA)⁻¹⁻¹ :=
  spW_conj (by decide) (by decide) idZ

theorem hs_comU (i : Nat) : hs i * uG * (hs i)⁻¹ = uG := by
  by_cases hi : i < 4
  · exact comm_ofK (allN_spec canonH i hi) canonU (allN_spec comU i hi) (hs_rep hi) uG_rep
  · rw [hs_ge hi]
    group

theorem hs_comZ (i : Nat) : hs i * zG * (hs i)⁻¹ = zG := by
  by_cases hi : i < 4
  · exact comm_ofK (allN_spec canonH i hi) canonZ (allN_spec comZ i hi) (hs_rep hi) zG_rep
  · rw [hs_ge hi]
    group

theorem rp0_rep : RepW 315 (RP0.map (unpack 315 9)) (spW UM) := by
  have e : RP0 = UM.map PJ2.S := rfl
  rw [e]
  exact spW_rep _ (by decide)

theorem rq1_rep : RepW 315 (RQ1.map (unpack 315 9)) (spW ZM) := by
  have h := spW_rep ZM (by decide)
  rw [zm_eq] at h
  exact repW_ofK (zm_eq ▸ rangeS ZM (by decide)) canonQ1 agQ1 h

theorem bIf_t {c t e : Bool} (hc : c = true)
    (h : Bool.rec (motive := fun _ => Bool) e t c = true) : t = true := by
  subst hc
  exact h

theorem bIf_f {c t e : Bool} (hc : c = false)
    (h : Bool.rec (motive := fun _ => Bool) e t c = true) : e = true := by
  subst hc
  exact h

theorem blt_t {a b : Nat} (h : Nat.blt a b = true) : a < b := Nat.le_of_ble_eq_true h

theorem forest_at {a : Nat} (ha : a < 315) : pg 9 (mask 9) OJP a < 33 ∧
    (pg 9 (mask 9) DEP a = 0 → pg 9 (mask 9) RTP (pg 9 (mask 9) OJP a) = a) ∧
    (pg 9 (mask 9) DEP a ≠ 0 → pg 9 (mask 9) PAR a < 315 ∧
      pg 9 (mask 9) OJP (pg 9 (mask 9) PAR a) = pg 9 (mask 9) OJP a ∧
      pg 9 (mask 9) DEP (pg 9 (mask 9) PAR a) + 1 = pg 9 (mask 9) DEP a ∧
      pg 9 (mask 9) GIP a < 4 ∧
      evRK 9 [HL.getD (pg 9 (mask 9) GIP a) 0] (pg 9 (mask 9) PAR a) = a) := by
  have h := allN_spec forest a ha
  simp only [Cnt3P.bAnd_and, Bool.and_eq_true] at h
  refine ⟨blt_t h.1, fun hd => ?_, fun hd => ?_⟩
  · have hb : Nat.beq (pg 9 (mask 9) DEP a) 0 = true := by rw [hd]; rfl
    exact Nat.eq_of_beq_eq_true (bIf_t hb h.2)
  · have hb : Nat.beq (pg 9 (mask 9) DEP a) 0 = false := Cnt3P.beq_false_iff.2 hd
    have h2 := bIf_f hb h.2
    simp only [Bool.and_eq_true] at h2
    obtain ⟨p1, p2, p3, p4, p5⟩ := h2
    exact ⟨blt_t p1, Nat.eq_of_beq_eq_true p2, Nat.eq_of_beq_eq_true p3, blt_t p4,
      Nat.eq_of_beq_eq_true p5⟩

theorem hs_edge {a i p : Nat} (ha : a < 315) (hi : i < 4) (hp : p < 315)
    (e : evRK 9 [HL.getD i 0] p = a) : hs i (pt p) = pt a := by
  refine Fin.ext ?_
  rw [← hs_rep hi (pt p), pt_val p hp, pt_val a ha,
    ← (Cnt3P.evRK_eq (Cnt3P.rangeL_of_canonL (allN_spec canonH i hi)) p hp).1, e]

theorem img_surj {r : Nat} (hr : r < 315) : ∃ k < 315, img k = r := by
  obtain ⟨k, hk, e⟩ := Finset.surj_on_of_inj_on_of_card_le (s := Finset.range 315)
    (t := Finset.range 315) (fun k _ => img k)
    (fun k hk => Finset.mem_range.2 (img_range k (Finset.mem_range.1 hk)))
    (fun k k' hk hk' e => img_inj k k' (Finset.mem_range.1 hk) (Finset.mem_range.1 hk') e) le_rfl
    r (Finset.mem_range.2 hr)
  exact ⟨k, Finset.mem_range.1 hk, e.symm⟩

@[expose] noncomputable def KJ (j : Nat) : Nat :=
  rpos 9 (mask 9) (Nat.mul 315 9) (PJ2.LR 0) (pg 9 (mask 9) RTP j)

theorem KJ_spec {j : Nat} (hj : j < 33) : KJ j < 315 ∧ img (KJ j) = pg 9 (mask 9) RTP j := by
  obtain ⟨k, hk, e⟩ := img_surj (blt_t (allN_spec rtlt j hj))
  have e' : KJ j = k := by
    rw [KJ, ← e, img_eq k hk]
    exact Nat.eq_of_beq_eq_true (allN_spec img0 k hk)
  rw [e']
  exact ⟨hk, e⟩

end CertificateChecks.KernelSporSch.PJ2Fib

end
