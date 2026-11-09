module

public import Certificates.Kernel.SporSch.Tits.T614D
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.PcompFacts

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.T614

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.BfsPin
open CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Monster.B.Co2 CFSG.Quasithin.H13.Tits614
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Tits2264
open CertificateChecks.KernelSpor.Tits2268 CertificateChecks.KernelMisc
open CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.TitsCommon
open CertificateChecks.KernelSporSch.TitsHelp CertificateChecks.KernelSporSch.TitsAbel

theorem id_eq : idA 1755 = unpack 1755 11 (pidn 1755 11) := (idK_sound idOK).symm

theorem fix_check_k : allLt 1755 (fun x => decide (x < 3) ||
    !(allLt 3 fun j => (titsRArrs[j]!)[x]! == x)) = true := by
  rw [allLt_eq_allN (g := fun x => decide (x < 3) ||
      !(allN 3 fun j => pg 11 (mask 11) (TitsR.S j) x == x)) fun x hx => by
    rw [allLt_eq_allN (g := fun j => pg 11 (mask 11) (TitsR.S j) x == x) fun j hj => by
      rw [r_get (by omega), unpack_get hx]]]
  quickRfl

theorem pW : wordEqK 1755 11 (mask 11) (pidn 1755 11) TitsH.S TitsH.SI 9 pWord T614P = true := by
  unfold wordEqK
  quickRfl

theorem p_eq : pArr = unpack 1755 11 T614P :=
  (wordEqK_sound ⟨bindsH.2.2.2.1, bindsH.2.2.2.2.1⟩ permH pW).1

theorem cP : C T614P := by quickRfl
theorem cPI : C (pinv T614P) := by quickRfl
theorem permP' : permOK 1755 11 (mask 11) (1755 * 11) T614P (pinv T614P) = true := by quickRfl

theorem pI_eq : invCand 1755 pArr = unpack 1755 11 (pinv T614P) := by
  rw [p_eq]
  exact invCand_unpack permP'

theorem p_check_k : lettersOK 3 pWord = true ∧ eqA 1755 (pow5Arr pArr) (idA 1755) = true := by
  refine ⟨by decide, ?_⟩
  unfold pow5Arr
  rw [p_eq, cu cP cP, cu cP (cc cP cP), cu cP (cc cP (cc cP cP)),
    cu cP (cc cP (cc cP (cc cP cP))), id_eq,
    eqA_unpack (cc cP (cc cP (cc cP (cc cP cP)))) canId]
  quickRfl

@[expose] noncomputable def wJ (wd : List Int) : Nat :=
  wordK 1755 11 (mask 11) (pidn 1755 11) TitsJ.S TitsJ.SI wd

@[expose] noncomputable def cmK (u v : Nat) : Nat := pc (pc (pc (pinv u) (pinv v)) u) v

@[expose] noncomputable def okJ (wd : List Int) : Bool :=
  bAnd(wordEqK 1755 11 (mask 11) (pidn 1755 11) TitsJ.S TitsJ.SI 9 wd (wJ wd),
  bAnd(canonK 1755 11 (mask 11) (1755 * 11) (wJ wd),
  bAnd(canonK 1755 11 (mask 11) (1755 * 11) (pinv (wJ wd)),
    permOK 1755 11 (mask 11) (1755 * 11) (wJ wd) (pinv (wJ wd)))))

theorem okJ_spec {wd : List Int} (h : okJ wd = true) :
    wordArr 1755 titsJArrs wd = unpack 1755 11 (wJ wd) ∧ C (wJ wd) ∧ C (pinv (wJ wd)) ∧
      invCand 1755 (unpack 1755 11 (wJ wd)) = unpack 1755 11 (pinv (wJ wd)) := by
  unfold okJ at h
  obtain ⟨h1, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h2, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h3, h4⟩ := (bAnd_iff _ _).1 h
  exact ⟨(wordEqK_sound ⟨bindsJ.2.2.2.1, bindsJ.2.2.2.2.1⟩ permJ h1).1, h2, h3,
    invCand_unpack h4⟩

def jWords614 : List (List Int) := [[1], [2], [1, 2], [1, 3], [1, 4], [2, 3]]

theorem jWords614_mem : ∀ i < 5, eXWord i ∈ jWords614 ∧ eYWord i ∈ jWords614 := by decide

theorem kOkJ : jWords614.all okJ = true := by
  unfold jWords614 okJ wordEqK
  quickRfl

theorem kEG : allN 5 (fun i => bAnd(Nat.beq (cmK (wJ (eXWord i)) (wJ (eYWord i))) (T614EG.getD i 0),
    canonK 1755 11 (mask 11) (1755 * 11) (T614EG.getD i 0))) = true := by quickRfl

theorem cEG {i : Nat} (hi : i < 5) : C (T614EG.getD i 0) :=
  ((bAnd_iff _ _).1 (allN_spec kEG i hi)).2

theorem eg_eq {i : Nat} (hi : i < 5) : eGenArr i = unpack 1755 11 (T614EG.getD i 0) := by
  obtain ⟨mx, my⟩ := jWords614_mem i hi
  have hx := List.all_eq_true.1 kOkJ _ mx
  have hy := List.all_eq_true.1 kOkJ _ my
  obtain ⟨ex, cx, cxi, ix⟩ := okJ_spec hx
  obtain ⟨ey, cy, cyi, iy⟩ := okJ_spec hy
  unfold eGenArr eXArr eYArr commArr
  rw [ex, ey, ix, iy, cu cxi cyi, cu (cc cxi cyi) cx, cu (cc (cc cxi cyi) cx) cy]
  have e := Nat.eq_of_beq_eq_true ((bAnd_iff _ _).1 (allN_spec kEG i hi)).1
  unfold cmK at e
  rw [e]

@[expose] noncomputable def epK (v : Nat) : Nat :=
  (List.range 5).foldl (fun a i => if v.testBit i then pc a (T614EG.getD i 0) else a)
    (pidn 1755 11)

theorem fold_eq (v : Nat) : ∀ (l : List Nat), (∀ i ∈ l, i < 5) → ∀ a, C a →
    l.foldl (fun A i => if v.testBit i then compA 1755 A (eGenArr i) else A) (unpack 1755 11 a) =
      unpack 1755 11 (l.foldl (fun a i => if v.testBit i then pc a (T614EG.getD i 0) else a) a) ∧
    C (l.foldl (fun a i => if v.testBit i then pc a (T614EG.getD i 0) else a) a)
  | [], _, a, ha => ⟨rfl, ha⟩
  | i :: l, hl, a, ha => by
    have hi : i < 5 := hl i List.mem_cons_self
    have hl' : ∀ j ∈ l, j < 5 := fun j hj => hl j (List.mem_cons_of_mem _ hj)
    simp only [List.foldl_cons]
    by_cases hb : v.testBit i = true
    · rw [ite_eq_left hb, ite_eq_left hb, eg_eq hi, cu ha (cEG hi)]
      exact fold_eq v l hl' _ (cc ha (cEG hi))
    · rw [ite_eq_right hb, ite_eq_right hb]
      exact fold_eq v l hl' a ha

theorem epK_eq (v : Nat) : eProdArr v = unpack 1755 11 (epK v) ∧ C (epK v) := by
  unfold eProdArr epK
  rw [id_eq]
  exact fold_eq v _ (fun i hi => List.mem_range.1 hi) _ canId

theorem el_eq : T614EL = (List.range 32).map epK := by decide +kernel

theorem eArrs_eq : eArrs = T614EL.map (unpack 1755 11) := by
  unfold eArrs
  rw [el_eq, List.map_map]
  exact List.map_congr_left fun v _ => (epK_eq v).1

theorem strictB_eq614 (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem permOK_self614 {c : Nat} (hc : C c) (h2 : pc c c = pidn 1755 11) :
    permOK 1755 11 (mask 11) (1755 * 11) c c = true := by
  obtain ⟨hn, hw, h0, hr⟩ := PF.canon_facts hc
  have hn32 : 1755 < 2 ^ 32 := by omega
  have h0' : Nat.shiftRight c (1755 * 11) = 0 := h0
  unfold permOK
  rw [bAnd_iff, bAnd_iff, h0']
  refine ⟨rfl, rfl, allN_of_forall fun i hi => ?_⟩
  rw [strictB_eq614, bAnd_iff]
  refine ⟨by simpa [Nat.blt_eq] using hr i hi, ?_⟩
  have e : pg 11 (mask 11) (pc c c) i = pg 11 (mask 11) (pidn 1755 11) i := by rw [h2]
  unfold pc at e
  rw [PF.pg_pcomp hn32 hi, PF.pg_pidn hn hw hi] at e
  rw [e]
  exact Nat.beq_refl _

theorem cEL {c : Nat} (hc : c ∈ T614EL) : C c := by
  rw [el_eq, List.mem_map] at hc
  obtain ⟨v, -, rfl⟩ := hc
  exact (epK_eq v).2

theorem el_getD {v : Nat} (hv : v < 32) : T614EL.getD v 0 = epK v := by
  rw [el_eq]
  simp [hv]

theorem ep_eq {v : Nat} (hv : v < 32) : eProdArr v = unpack 1755 11 (T614EL.getD v 0) := by
  rw [el_getD hv]
  exact (epK_eq v).1

theorem cEp {v : Nat} (hv : v < 32) : C (T614EL.getD v 0) := by
  rw [el_getD hv]
  exact (epK_eq v).2

theorem inE_eq {x : Nat} (hx : C x) : inE (unpack 1755 11 x) = T614EL.any (Nat.beq x) := by
  unfold inE anyEq
  rw [eArrs_eq]
  exact any_eqA_unpack hx fun q hq => cEL hq

theorem inJ_eq {X : Nat} (hX : C X) : inJ (unpack 1755 11 X) = sfJ X :=
  siftK_eq bindsJ permJ TitsJ.hl rfl (hi_of hX) (range_of_canonK hX)

theorem inK_eq {X : Nat} (hX : C X) : inK (unpack 1755 11 X) = sfK X :=
  siftK_eq bindsK permK TitsK.hl rfl (hi_of hX) (range_of_canonK hX)

theorem kE3 : allN 5 (fun i => T614EL.any (Nat.beq (T614EG.getD i 0))) = true := by quickRfl

theorem pc_assoc_t614 {p r : Nat} (q : Nat) (hp : C p) (hr : C r) :
    pc (pc p q) r = pc p (pc q r) := by
  obtain ⟨hn, hw, -, -⟩ := PF.canon_facts hp
  obtain ⟨-, -, -, hrr⟩ := PF.canon_facts hr
  have hn32 : 1755 < 2 ^ 32 := by omega
  have hw0 := PF.w_pos hw
  unfold pc
  refine PF.eq_of_fields hw0 (PF.pcomp_shr _ _ hn32 hw0) (PF.pcomp_shr _ _ hn32 hw0) fun i hi => ?_
  rw [PF.pg_pcomp hn32 hi, PF.pg_pcomp hn32 (hrr i hi), PF.pg_pcomp hn32 hi,
    PF.pg_pcomp hn32 hi]

theorem pc_pidn_t614 {p : Nat} (hp : C p) : pc p (pidn 1755 11) = p := by
  obtain ⟨hn, hw, hp0, -⟩ := PF.canon_facts hp
  have hn32 : 1755 < 2 ^ 32 := by omega
  have hw0 := PF.w_pos hw
  unfold pc
  refine PF.eq_of_fields hw0 (PF.pcomp_shr _ _ hn32 hw0) hp0 fun i hi => ?_
  rw [PF.pg_pcomp hn32 hi, PF.pg_pidn hn hw hi]

theorem kE4X : allN 32 (fun v => allN 5 (fun i =>
    Nat.beq (pc (T614EL.getD v 0) (T614EG.getD i 0)) (T614EL.getD (v ^^^ 2 ^ i) 0))) = true := by
  quickRfl

theorem elId614 : T614EL.getD 0 0 = pidn 1755 11 := by
  rw [el_getD (by norm_num)]
  rfl

theorem elMem {u : Nat} (hu : u < 32) : T614EL.getD u 0 ∈ T614EL := by
  rw [el_getD hu, el_eq]
  exact List.mem_map.2 ⟨u, List.mem_range.2 hu, rfl⟩

theorem xorLt614 : ∀ a < 32, ∀ b < 32, a ^^^ b < 32 := by decide +kernel

theorem dropBit32 : ∀ w < 32, w ≠ 0 → ∃ i < 5, w ^^^ 2 ^ i < w := by decide +kernel

theorem mulEL : ∀ w, w < 32 → ∀ v, v < 32 →
    pc (T614EL.getD v 0) (T614EL.getD w 0) = T614EL.getD (v ^^^ w) 0 := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw v hv
    by_cases h0 : w = 0
    · subst h0
      rw [elId614, pc_pidn_t614 (cEp hv), Nat.xor_zero]
    · obtain ⟨i, hi, hlt⟩ := dropBit32 w hw h0
      have hw' : w ^^^ 2 ^ i < 32 := by omega
      have e1 : (w ^^^ 2 ^ i) ^^^ 2 ^ i = w := by
        rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
      have hg : pc (T614EL.getD (w ^^^ 2 ^ i) 0) (T614EG.getD i 0) = T614EL.getD w 0 := by
        have := Nat.eq_of_beq_eq_true (allN_spec (allN_spec kE4X _ hw') i hi)
        rw [e1] at this
        exact this
      rw [← hg, ← pc_assoc_t614 _ (cEp hv) (cEG hi), ih _ hlt hw' v hv]
      have := Nat.eq_of_beq_eq_true (allN_spec (allN_spec kE4X _ (xorLt614 v hv _ hw')) i hi)
      rw [this, Nat.xor_assoc, e1]

theorem kE4 : allN 32 (fun v => allN 32 (fun w =>
    T614EL.any (Nat.beq (pc (T614EL.getD v 0) (T614EL.getD w 0))) &&
      Nat.beq (pc (T614EL.getD v 0) (T614EL.getD w 0)) (pc (T614EL.getD w 0) (T614EL.getD v 0))))
    = true := by
  refine allN_of_forall fun v hv => allN_of_forall fun w hw => ?_
  rw [mulEL w hw v hv, mulEL v hv w hw, Nat.xor_comm w v, Nat.beq_refl, Bool.and_true]
  exact List.any_eq_true.2 ⟨_, elMem (xorLt614 v hv w hw), Nat.beq_refl _⟩

theorem kE5 : allN 32 (fun v => Nat.beq (pc (T614EL.getD v 0) (T614EL.getD v 0)) (pidn 1755 11)) =
    true := by
  refine allN_of_forall fun v hv => ?_
  rw [mulEL v hv v hv, Nat.xor_self, elId614]
  exact Nat.beq_refl _

theorem elPerm614 {c : Nat} (hc : c ∈ T614EL) : permOK 1755 11 (mask 11) (1755 * 11) c c = true := by
  have hc' := hc
  rw [el_eq, List.mem_map] at hc'
  obtain ⟨v, hv, rfl⟩ := hc'
  have hv' := List.mem_range.1 hv
  refine permOK_self614 (cEL hc) ?_
  rw [← el_getD hv', mulEL v hv' v hv', Nat.xor_self, elId614]

theorem kE6 : T614EL.Pairwise (fun a b => Nat.beq a b = false) := by decide +kernel

theorem kE8 : allN 32 (fun v => sfJ (T614EL.getD v 0) && sfK (T614EL.getD v 0)) = true := by
  quickRfl

theorem kE9 : allN 5 (fun i =>
    T614EL.any (Nat.beq (pc (pc T614P (T614EG.getD i 0)) (pinv T614P)))) = true := by quickRfl

theorem kE10 : T614EL.any (Nat.beq TitsZ) = true := by quickRfl

theorem eck_1 : (∀ i < 5, lettersOK 4 (eXWord i) = true ∧ lettersOK 4 (eYWord i) = true) := by
  decide

theorem eck_2 :
    eqA 1755 (eProdArr 0) (idA 1755) = true := by
  rw [ep_eq (by norm_num), id_eq, eqA_unpack (cEp (by norm_num)) canId]
  quickRfl

theorem eck_3 :
    (allLt 5 fun i => inE (eGenArr i)) = true := by
  rw [allLt_eq_allN (g := fun i => T614EL.any (Nat.beq (T614EG.getD i 0))) fun i hi => by
    rw [eg_eq hi, inE_eq (cEG hi)]]
  exact kE3

theorem eck_4 :
    (allLt 32 fun v => allLt 32 fun w => inE (compA 1755 (eProdArr v) (eProdArr w)) &&
      eqA 1755 (compA 1755 (eProdArr v) (eProdArr w))
        (compA 1755 (eProdArr w) (eProdArr v))) = true := by
  rw [allLt_eq_allN (g := fun v => allN 32 (fun w =>
    T614EL.any (Nat.beq (pc (T614EL.getD v 0) (T614EL.getD w 0))) &&
      Nat.beq (pc (T614EL.getD v 0) (T614EL.getD w 0)) (pc (T614EL.getD w 0) (T614EL.getD v 0))))
    fun v hv => by
      rw [allLt_eq_allN fun w hw => by
        rw [ep_eq hv, ep_eq hw, cu (cEp hv) (cEp hw), cu (cEp hw) (cEp hv),
          inE_eq (cc (cEp hv) (cEp hw)), eqA_unpack (cc (cEp hv) (cEp hw)) (cc (cEp hw) (cEp hv))]]]
  exact kE4

theorem eck_5 :
    (allLt 32 fun v => eqA 1755 (compA 1755 (eProdArr v) (eProdArr v)) (idA 1755)) = true := by
  rw [allLt_eq_allN (g := fun v => Nat.beq (pc (T614EL.getD v 0) (T614EL.getD v 0))
    (pidn 1755 11)) fun v hv => by
      rw [ep_eq hv, cu (cEp hv) (cEp hv), id_eq, eqA_unpack (cc (cEp hv) (cEp hv)) canId]]
  exact kE5

theorem eck_6 :
    eArrs.Pairwise (fun a b => eqA 1755 a b = false) := by
  rw [eArrs_eq, List.pairwise_map]
  refine kE6.imp_of_mem fun {a b} ha hb h => ?_
  rw [eqA_unpack (cEL ha) (cEL hb)]
  exact h

theorem eck_7 :
    eArrs.all (fun c => isInvA 1755 c (invCand 1755 c)) = true := by
  rw [eArrs_eq, List.all_eq_true]
  intro c' hc'
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hc'
  obtain ⟨h1, h2⟩ := invEqK_sound (r := c) (elPerm614 hc)
  have h3 : isInvA 1755 (unpack 1755 11 c) (invCand 1755 (unpack 1755 11 c)) = true := by
    rw [h1]
    exact h2
  exact h3

theorem eck_8 :
    (allLt 32 fun v => inJ (eProdArr v) && inK (eProdArr v)) = true := by
  rw [allLt_eq_allN (g := fun v => sfJ (T614EL.getD v 0) && sfK (T614EL.getD v 0)) fun v hv => by
    rw [ep_eq hv, inJ_eq (cEp hv), inK_eq (cEp hv)]]
  exact kE8

theorem eck_9 :
    (allLt 5 fun i => inE (conjArr pArr (eGenArr i))) = true := by
  rw [allLt_eq_allN (g := fun i =>
    T614EL.any (Nat.beq (pc (pc T614P (T614EG.getD i 0)) (pinv T614P)))) fun i hi => by
      unfold conjArr
      rw [eg_eq hi, pI_eq, p_eq, cu cP (cEG hi), cu (cc cP (cEG hi)) cPI,
        inE_eq (cc (cc cP (cEG hi)) cPI)]]
  exact kE9

theorem eck_10 :
    inE titsZArr = true := by
  rw [z_eq, inE_eq canonZ]
  exact kE10

theorem e_check_k :
    (∀ i < 5, lettersOK 4 (eXWord i) = true ∧ lettersOK 4 (eYWord i) = true) ∧
    eqA 1755 (eProdArr 0) (idA 1755) = true ∧ (allLt 5 fun i => inE (eGenArr i)) = true ∧
    (allLt 32 fun v => allLt 32 fun w => inE (compA 1755 (eProdArr v) (eProdArr w)) &&
      eqA 1755 (compA 1755 (eProdArr v) (eProdArr w))
        (compA 1755 (eProdArr w) (eProdArr v))) = true ∧
    (allLt 32 fun v => eqA 1755 (compA 1755 (eProdArr v) (eProdArr v)) (idA 1755)) = true ∧
    eArrs.Pairwise (fun a b => eqA 1755 a b = false) ∧
    eArrs.all (fun c => isInvA 1755 c (invCand 1755 c)) = true ∧
    (allLt 32 fun v => inJ (eProdArr v) && inK (eProdArr v)) = true ∧
    (allLt 5 fun i => inE (conjArr pArr (eGenArr i))) = true ∧ inE titsZArr = true :=
  ⟨eck_1, eck_2, eck_3, eck_4, eck_5, eck_6, eck_7, eck_8, eck_9, eck_10⟩

end CertificateChecks.KernelSporSch.T614

end
