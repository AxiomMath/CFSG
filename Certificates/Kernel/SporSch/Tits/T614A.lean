module

public import Certificates.Kernel.SporSch.Tits.T614D
import CFSG.Certificates.Kernel.Common.Harness

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

theorem kOkJ : allN 5 (fun i => bAnd(okJ (eXWord i), okJ (eYWord i))) = true := by
  unfold okJ wordEqK
  quickRfl

theorem kEG : allN 5 (fun i => bAnd(Nat.beq (cmK (wJ (eXWord i)) (wJ (eYWord i))) (T614EG.getD i 0),
    canonK 1755 11 (mask 11) (1755 * 11) (T614EG.getD i 0))) = true := by quickRfl

theorem cEG {i : Nat} (hi : i < 5) : C (T614EG.getD i 0) :=
  ((bAnd_iff _ _).1 (allN_spec kEG i hi)).2

theorem eg_eq {i : Nat} (hi : i < 5) : eGenArr i = unpack 1755 11 (T614EG.getD i 0) := by
  obtain ⟨hx, hy⟩ := (bAnd_iff _ _).1 (allN_spec kOkJ i hi)
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
    · rw [if_pos hb, if_pos hb, eg_eq hi, cu ha (cEG hi)]
      exact fold_eq v l hl' _ (cc ha (cEG hi))
    · rw [if_neg hb, if_neg hb]
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

theorem kEL : T614EL.all (fun c => bAnd(canonK 1755 11 (mask 11) (1755 * 11) c,
    permOK 1755 11 (mask 11) (1755 * 11) c (pinvS 1755 11 (mask 11) c))) = true := by quickRfl

theorem cEL {c : Nat} (hc : c ∈ T614EL) : C c :=
  ((bAnd_iff _ _).1 (List.all_eq_true.1 kEL c hc)).1

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

theorem kE4 : allN 32 (fun v => allN 32 (fun w =>
    T614EL.any (Nat.beq (pc (T614EL.getD v 0) (T614EL.getD w 0))) &&
      Nat.beq (pc (T614EL.getD v 0) (T614EL.getD w 0)) (pc (T614EL.getD w 0) (T614EL.getD v 0))))
    = true := by quickRfl

theorem kE5 : allN 32 (fun v => Nat.beq (pc (T614EL.getD v 0) (T614EL.getD v 0)) (pidn 1755 11)) =
    true := by quickRfl

theorem kE6 : T614EL.Pairwise (fun a b => Nat.beq a b = false) := by decide +kernel

theorem kE8 : allN 32 (fun v => sfJ (T614EL.getD v 0) && sfK (T614EL.getD v 0)) = true := by
  quickRfl

theorem kE9 : allN 5 (fun i =>
    T614EL.any (Nat.beq (pc (pc T614P (T614EG.getD i 0)) (pinv T614P)))) = true := by quickRfl

theorem kE10 : T614EL.any (Nat.beq TitsZ) = true := by quickRfl

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
    (allLt 5 fun i => inE (conjArr pArr (eGenArr i))) = true ∧ inE titsZArr = true := by
  refine ⟨by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ep_eq (by norm_num), id_eq, eqA_unpack (cEp (by norm_num)) canId]
    quickRfl
  · rw [allLt_eq_allN (g := fun i => T614EL.any (Nat.beq (T614EG.getD i 0))) fun i hi => by
      rw [eg_eq hi, inE_eq (cEG hi)]]
    exact kE3
  · rw [allLt_eq_allN (g := fun v => allN 32 (fun w =>
      T614EL.any (Nat.beq (pc (T614EL.getD v 0) (T614EL.getD w 0))) &&
        Nat.beq (pc (T614EL.getD v 0) (T614EL.getD w 0)) (pc (T614EL.getD w 0) (T614EL.getD v 0))))
      fun v hv => by
        rw [allLt_eq_allN fun w hw => by
          rw [ep_eq hv, ep_eq hw, cu (cEp hv) (cEp hw), cu (cEp hw) (cEp hv),
            inE_eq (cc (cEp hv) (cEp hw)), eqA_unpack (cc (cEp hv) (cEp hw)) (cc (cEp hw) (cEp hv))]]]
    exact kE4
  · rw [allLt_eq_allN (g := fun v => Nat.beq (pc (T614EL.getD v 0) (T614EL.getD v 0))
      (pidn 1755 11)) fun v hv => by
        rw [ep_eq hv, cu (cEp hv) (cEp hv), id_eq, eqA_unpack (cc (cEp hv) (cEp hv)) canId]]
    exact kE5
  · rw [eArrs_eq, List.pairwise_map]
    refine kE6.imp_of_mem fun {a b} ha hb h => ?_
    rw [eqA_unpack (cEL ha) (cEL hb)]
    exact h
  · rw [eArrs_eq, List.all_map, List.all_eq_true]
    intro c hc
    exact isInv_of ((bAnd_iff _ _).1 (List.all_eq_true.1 kEL c hc)).2
  · rw [allLt_eq_allN (g := fun v => sfJ (T614EL.getD v 0) && sfK (T614EL.getD v 0)) fun v hv => by
      rw [ep_eq hv, inJ_eq (cEp hv), inK_eq (cEp hv)]]
    exact kE8
  · rw [allLt_eq_allN (g := fun i =>
      T614EL.any (Nat.beq (pc (pc T614P (T614EG.getD i 0)) (pinv T614P)))) fun i hi => by
        unfold conjArr
        rw [eg_eq hi, pI_eq, p_eq, cu cP (cEG hi), cu (cc cP (cEG hi)) cPI,
          inE_eq (cc (cc cP (cEG hi)) cPI)]]
    exact kE9
  · rw [z_eq, inE_eq canonZ]
    exact kE10

end CertificateChecks.KernelSporSch.T614

end
