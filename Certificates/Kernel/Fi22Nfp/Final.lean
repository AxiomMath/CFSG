module

public import Certificates.Kernel.Fi22Nfp.Checks
public import Certificates.Kernel.Fi22Syl.Final
public import Certificates.Kernel.Fi22Cent.Final
import Certificates.Kernel.Sporadic.ON.Gen
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Spor.Loops
import Mathlib.Tactic.IntervalCases
public import Certificates.Data.CFSGNative.Fi22.Nfp

public section

set_option maxRecDepth 400000

#kon_join CertificateChecks.KernelFi22N.t6All CertificateChecks.KernelFi22N.t6Sl 14
#kon_join CertificateChecks.KernelFi22N.uConjAll CertificateChecks.KernelFi22N.uConj 6
#kon_join CertificateChecks.KernelFi22N.uRecAll CertificateChecks.KernelFi22N.uRecSl 14
#kon_join CertificateChecks.KernelFi22N.nfpAll CertificateChecks.KernelFi22N.nfpSl 128

namespace CertificateChecks.KernelFi22N

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.TBfs CFSG.KS.PC CFSG.KS.TW
  CFSG.KS.Fi22S CFSG.KS.Fi22Cent CFSG.KS.Fi22N CFSG.Sporadic.Fi22.Native
  CFSG.Sporadic.Th.Native CFSG.Perm.Native
  CertificateChecks.KernelFi22S CertificateChecks.KernelFi22Cent

theorem beq_nat (a b : Nat) : (a == b) = Nat.beq a b := by
  rw [Bool.eq_iff_iff, beq_iff_eq, Nat.beq_eq]

theorem nfpBase_size : nfpBase.size = 6 := rfl

theorem uImg_size : uImg.size = 6 := rfl

theorem nb_get {l : Nat} (hl : l < 6) : nfpBase[l]! = NB l ∧ NB l < 3510 := by
  interval_cases l <;> exact ⟨rfl, by decide⟩

theorem ui_get {l : Nat} (hl : l < 6) : uImg[l]! = UI l ∧ UI l < 3510 := by
  interval_cases l <;> exact ⟨rfl, by decide⟩

theorem cnts : CNTN 1 = 1 ∧ CNTN 2 = 3 ∧ CNTN 3 = 6 ∧ CNTN 4 = 36 ∧ CNTN 5 = 165 ∧
    CNTN 6 = 3510 := by
  have h := sizes_ok
  unfold sizesN at h
  simp only [Raw.Orb.bAnd_eq, Bool.and_eq_true, Nat.beq_eq] at h
  exact h

theorem uk_facts {x : Nat} (hx : x < 3510) : UK x < 3510 ∧ UK (UK x) = x := by
  have h := Raw.Orb.allN_iff.1 uInv_ok x hx
  simp only [Raw.Orb.strictB_eq, Raw.Orb.bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  exact h

theorem tabOf_ap {c x : Nat} (hc : c < 3510) (hx : x < 3510) : ap (tabOf orbL c) x = cK c x :=
  cTab_eq hc hx

theorem cTab_size (k : Nat) : (cTab orbL (genTables orbL (-2)) k).size = 3510 := by
  rw [cTab]
  split_ifs
  · simp [compT]
  · simp [compT]
  · exact CFSG.KS.Fi22L.orbTab_size 0

theorem pt_all {i : Nat} (hi1 : 1 ≤ i) (hi : i < 7) : ∀ k < CNTN i,
    tbfsPtK 3510 (CNTN i) i LC (fun t => t) (PTSN i) (POSN i) (PARN i) (LABN i) (TIN i) k = true := by
  intro k hk
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := cnts
  have hs := small_ok
  unfold smallK at hs
  simp only [Raw.Orb.bAnd_eq, Bool.and_eq_true] at hs
  obtain ⟨s1, s2, s3, s4, s5⟩ := hs
  have sl : ∀ {i lo len : Nat}, ptN i lo len = true → lo ≤ k → k < lo + len → k < CNTN i →
      tbfsPtK 3510 (CNTN i) i LC (fun t => t) (PTSN i) (POSN i) (PARN i) (LABN i) (TIN i) k =
        true := fun h h1 h2 h3 => KernelFi22S.sl_spec h k h1 h2 h3
  interval_cases i
  · exact sl s1 (Nat.zero_le k) (by rw [c1] at hk; change k < 256; omega) hk
  · exact sl s2 (Nat.zero_le k) (by rw [c2] at hk; change k < 256; omega) hk
  · exact sl s3 (Nat.zero_le k) (by rw [c3] at hk; change k < 256; omega) hk
  · exact sl s4 (Nat.zero_le k) (by rw [c4] at hk; change k < 256; omega) hk
  · exact sl s5 (Nat.zero_le k) (by rw [c5] at hk; change k < 256; omega) hk
  · have hs6 : k / 256 < 14 := by rw [c6] at hk; omega
    exact sl (t6All (k / 256) hs6) (by change k / 256 * 256 ≤ k; omega)
      (by change k < k / 256 * 256 + 256; omega) hk

noncomputable abbrev tbN : Array Table := nfpBase.map (tabOf orbL)

theorem tb_get {l : Nat} (hl : l < 6) : ∀ x < 3510, ap tbN[l]! x = LC l x := by
  intro x hx
  obtain ⟨e, hb⟩ := nb_get hl
  have e2 : tbN[l]! = tabOf orbL nfpBase[l]! := by
    rw [getElem!_pos _ l (by rw [Array.size_map, nfpBase_size]; exact hl), Array.getElem_map,
      getElem!_pos nfpBase l (by rw [nfpBase_size]; exact hl)]
  rw [e2, e]
  exact tabOf_ap hb hx

theorem clos_eq {i : Nat} (hi1 : 1 ≤ i) (hi : i < 7) :
    closTree tbN i = tbfsRec 3510 (CNTN i) (PTSN i) (POSN i) (PARN i) (LABN i) ∧
      closOK tbN i = true := by
  have hh : tbfsHdK 3510 641 (CNTN i) (PTSN i) (POSN i) (PARN i) (LABN i) = true := by
    have hi' : i - 1 < 6 := by omega
    have h := Raw.Orb.allN_iff.1 hd_ok (i - 1) hi'
    have e : Nat.succ (i - 1) = i := by omega
    rw [e] at h
    exact h
  have hT := tbfsK_sound (n := 3510) (root := 641) (letters := tbN) (lv := Array.range i)
    (L := LC) (LV := fun t => t)
    ⟨by simp, fun t ht => ⟨by rw [getElem!_pos _ t (by simpa using ht), Array.getElem_range],
      by rw [Array.size_map, nfpBase_size]; omega, tb_get (by omega)⟩⟩ hh (pt_all hi1 hi)
  have e0 : nfpBase[0]! = 641 := rfl
  have h1 : closTree tbN i = tbfsRec 3510 (CNTN i) (PTSN i) (POSN i) (PARN i) (LABN i) := by
    unfold closTree
    rw [e0]
    exact hT.1
  refine ⟨h1, ?_⟩
  unfold closOK
  rw [h1, e0]
  exact hT.2

theorem pts_lt {i : Nat} (hi1 : 1 ≤ i) (hi : i < 7) {k : Nat} (hk : k < CNTN i) :
    r32 (PTSN i) k < 3510 := (pt_spec (pt_all hi1 hi k hk)).lt

theorem ap_pts {i : Nat} {k : Nat} (hk : k < CNTN i) :
    ap (tbfsRec 3510 (CNTN i) (PTSN i) (POSN i) (PARN i) (LABN i)).pts k = r32 (PTSN i) k := by
  unfold tbfsRec
  rw [CFSG.Sporadic.Th.ap_ofFn _ hk, toNat_r32]

theorem ap_par {i : Nat} {k : Nat} (hk : k < CNTN i) :
    ap (tbfsRec 3510 (CNTN i) (PTSN i) (POSN i) (PARN i) (LABN i)).par k = r32 (PARN i) k := by
  unfold tbfsRec
  rw [CFSG.Sporadic.Th.ap_ofFn _ hk, toNat_r32]

theorem ap_lab {i : Nat} {k : Nat} (hk : k < CNTN i) :
    ap (tbfsRec 3510 (CNTN i) (PTSN i) (POSN i) (PARN i) (LABN i)).lab k = r32 (LABN i) k := by
  unfold tbfsRec
  rw [CFSG.Sporadic.Th.ap_ofFn _ hk, toNat_r32]

theorem foldr_countP (p : Nat → Bool) : ∀ l : List Nat,
    l.foldr (fun v s => Bool.rec (motive := fun _ => Nat) s (Nat.succ s) (p v)) 0 = l.countP p
  | [] => rfl
  | a :: l => by
    rw [List.foldr_cons, foldr_countP p l, List.countP_cons]
    cases p a <;> rfl

theorem relKey_eq {c v : Nat} {C : Table} (hC : ∀ x < 3510, ap C x = cK c x) (hv : v < 3510) :
    relKey c C v = relK c v := by
  unfold relKey relK
  rw [Raw.Orb.nIf_eq, Raw.Orb.nIf_eq, hC v hv, beq_nat, beq_nat]

theorem cand_eq {i : Nat} (hi1 : 1 ≤ i) (hi : i < 6) :
    candCount orbL tbN i = cntC i := by
  have hc := (clos_eq hi1 (by omega)).1
  have hb := nb_get (l := i) (by omega)
  unfold candCount cntC
  rw [Raw.Orb.foldN_eq, foldr_countP, hc]
  apply List.countP_congr
  intro v hv
  have hv' := List.mem_range.1 hv
  unfold candAt candK
  rw [TW.allIn_iff, Raw.Orb.allN_iff]
  have hs : (tbfsRec 3510 (CNTN i) (PTSN i) (POSN i) (PARN i) (LABN i)).pts.size = CNTN i := by
    simp [tbfsRec]
  rw [hs, hb.1]
  suffices key : ∀ k < CNTN i,
      (relKey (ap (tbfsRec 3510 (CNTN i) (PTSN i) (POSN i) (PARN i) (LABN i)).pts k)
        ((tbfsRec 3510 (CNTN i) (PTSN i) (POSN i) (PARN i) (LABN i)).pts.map
          fun c => tabOf orbL c.toNat)[k]! v ==
      relKey (ap (tbfsRec 3510 (CNTN i) (PTSN i) (POSN i) (PARN i) (LABN i)).pts k)
        ((tbfsRec 3510 (CNTN i) (PTSN i) (POSN i) (PARN i) (LABN i)).pts.map
          fun c => tabOf orbL c.toNat)[k]! (NB i)) =
      strictB (r32 (PTSN i) k) fun c => Nat.beq (relK c v) (relK c (NB i)) by
    constructor
    · intro h k hk
      rw [← key k hk]
      exact h k hk
    · intro h k hk
      rw [key k hk]
      exact h k hk
  intro k hk
  have hp := pts_lt hi1 (by omega) hk
  have hcs : ∀ x < 3510, ap ((tbfsRec 3510 (CNTN i) (PTSN i) (POSN i) (PARN i) (LABN i)).pts.map
      fun c => tabOf orbL c.toNat)[k]! x = cK (r32 (PTSN i) k) x := by
    intro x hx
    rw [getElem!_pos _ k (by simp [tbfsRec]; exact hk), Array.getElem_map]
    have e : ((tbfsRec 3510 (CNTN i) (PTSN i) (POSN i) (PARN i) (LABN i)).pts[k]'(by
        simp [tbfsRec]; exact hk)).toNat = r32 (PTSN i) k := by
      rw [← ap_pts hk, ap, getElem!_pos _ k (by simp [tbfsRec]; exact hk)]
    rw [e]
    exact tabOf_ap hp hx
  rw [ap_pts hk, Raw.Orb.strictB_eq, relKey_eq hcs hv', relKey_eq hcs hb.2, beq_nat]

theorem candNAll (i : Nat) (hi1 : 1 ≤ i) (hi : i < 6) : candN i = true := by
  interval_cases i
  · exact candN1
  · exact candN2
  · exact candN3
  · exact candN4
  · exact candN5

theorem bounds_get {i : Nat} (hi : i < 6) :
    nfpBounds[i]! = List.getD [3510, 2816, 567, 720, 16, 2] i 0 := by
  interval_cases i <;> rfl

noncomputable abbrev F6 : Tree := tbfsRec 3510 (CNTN 6) (PTSN 6) (POSN 6) (PARN 6) (LABN 6)

noncomputable abbrev tcN : Array Table := uImg.map (tabOf orbL)

theorem tc_get {l : Nat} (hl : l < 6) : ∀ x < 3510, ap tcN[l]! x = cK (UI l) x := by
  intro x hx
  obtain ⟨e, hb⟩ := ui_get hl
  have e2 : tcN[l]! = tabOf orbL uImg[l]! := by
    rw [getElem!_pos _ l (by rw [Array.size_map, uImg_size]; exact hl), Array.getElem_map,
      getElem!_pos uImg l (by rw [uImg_size]; exact hl)]
  rw [e2, e]
  exact tabOf_ap hb hx

theorem rec_facts {k : Nat} (hk0 : 0 < k) (hk : k < 3510) :
    r32 (PARN 6) k < k ∧ r32 (LABN 6) k < 6 ∧
      UK (r32 (PTSN 6) k) = cK (UI (r32 (LABN 6) k)) (UK (r32 (PTSN 6) (r32 (PARN 6) k))) := by
  have c6 := cnts.2.2.2.2.2
  have hp := pt_spec (pt_all (i := 6) (by norm_num) (by norm_num) k (by rw [c6]; exact hk))
  obtain ⟨a1, a2, a3, -, -⟩ := hp.tree hk0
  refine ⟨a1, by rw [a3]; exact a2, ?_⟩
  have hs : k / 256 < 14 := by omega
  have h := uRecAll (k / 256) hs
  unfold uRecSl at h
  rw [Raw.Orb.bAnd_eq, Bool.and_eq_true] at h
  have h' := Raw.Orb.allN_iff.1 h.2 (k % 256) (Nat.mod_lt _ (by norm_num))
  rw [Raw.Orb.strictB_eq] at h'
  have e : Nat.add (Nat.mul (k / 256) 256) (k % 256) = k := Nat.div_add_mod' k 256
  rw [e, Raw.Orb.bIf_eq] at h'
  have hc : bAnd(Nat.blt 0 k, Nat.blt k 3510) = true := by
    rw [Raw.Orb.bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.blt_eq]
    exact ⟨hk0, hk⟩
  rw [ite_eq_left hc, Nat.beq_eq] at h'
  exact h'

theorem rec_root : UK (r32 (PTSN 6) 0) = UI 0 := by
  have h := uRecAll 0 (by norm_num)
  unfold uRecSl at h
  rw [Raw.Orb.bAnd_eq, Bool.and_eq_true, Nat.beq_eq] at h
  exact h.1

theorem ap_eq_of_get {t : Table} {p : Nat} {v : UInt32} (h : t[p]! = v) : ap t p = v.toNat := by
  unfold ap
  rw [h]

structure RecHyp (T : Tree) (tc : Array Table) (P PA LB POS V : Nat → Nat) : Prop where
  size : T.pts.size = 3510
  pts : ∀ k < 3510, ap T.pts k = P k
  par : ∀ k < 3510, ap T.par k = PA k
  lab : ∀ k < 3510, ap T.lab k = LB k
  plt : ∀ k < 3510, P k < 3510
  pos : ∀ k < 3510, POS (P k) = k
  step : ∀ k, 0 < k → k < 3510 → PA k < k ∧ LB k < 6 ∧ V k = cK (UI (LB k)) (V (PA k))
  root : V 0 = UI 0
  vlt : ∀ k < 3510, V k < 3510
  tc : ∀ l < 6, ∀ x < 3510, ap tc[l]! x = cK (UI l) x

section Recon

variable {T : Tree} {tc : Array Table} {P PA LB POS V : Nat → Nat}

theorem im_loop (H : RecHyp T tc P PA LB POS V) : ∀ j, j + 1 ≤ 3510 →
    ((List.range' 1 j).foldl (fun im k => im.set! k (ap tc[ap T.lab k]! im[ap T.par k]!))
      ((Array.replicate 3510 0).set! 0 (UI 0))).size = 3510 ∧
    ∀ k ≤ j, ((List.range' 1 j).foldl (fun im k => im.set! k (ap tc[ap T.lab k]! im[ap T.par k]!))
      ((Array.replicate 3510 0).set! 0 (UI 0)))[k]! = V k
  | 0, _ => by
    refine ⟨by simp, fun k hk => ?_⟩
    have : k = 0 := by omega
    subst this
    simp only [List.range'_zero, List.foldl_nil]
    rw [Array.set!_eq_setIfInBounds, getElem!_pos _ 0 (by simp), Array.getElem_setIfInBounds_self,
      H.root]
  | j + 1, hj => by
    obtain ⟨hs, hv⟩ := im_loop H j (by omega)
    rw [List.range'_1_concat, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize (List.range' 1 j).foldl (fun im k => im.set! k (ap tc[ap T.lab k]! im[ap T.par k]!))
      ((Array.replicate 3510 0).set! 0 (UI 0)) = im at hs hv
    obtain ⟨p1, l1, r1⟩ := H.step (1 + j) (by omega) (by omega)
    have hsz : (im.set! (1 + j) (ap tc[ap T.lab (1 + j)]! im[ap T.par (1 + j)]!)).size = 3510 := by
      rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, hs]
    refine ⟨hsz, fun k hk => ?_⟩
    rw [Array.set!_eq_setIfInBounds, getElem!_pos _ k (by rw [Array.size_setIfInBounds, hs]; omega)]
    by_cases e : k = 1 + j
    · subst e
      rw [Array.getElem_setIfInBounds_self, H.par _ (by omega), H.lab _ (by omega),
        hv _ (by omega), H.tc _ l1 _ (H.vlt _ (by omega)), r1]
    · rw [Array.getElem_setIfInBounds_ne (by rw [hs]; omega) (Ne.symm e),
        ← getElem!_pos im k (by rw [hs]; omega)]
      exact hv k (by omega)

theorem recon_eq (H : RecHyp T tc P PA LB POS V) : reconTab T tc (UI 0) =
    (List.range' 0 3510).foldl (fun U k => U.set! (ap T.pts k) (UInt32.ofNat
      ((List.range' 1 3509).foldl (fun im k => im.set! k (ap tc[ap T.lab k]! im[ap T.par k]!))
        ((Array.replicate 3510 0).set! 0 (UI 0)))[k]!)) (Array.replicate 3510 0) := by
  unfold reconTab
  simp only [H.size]
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.forIn_pure_yield_eq_foldl]

theorem recon_pt (H : RecHyp T tc P PA LB POS V) {k : Nat} (hk : k < 3510) :
    ap (reconTab T tc (UI 0)) (P k) = V k := by
  obtain ⟨-, hv⟩ := im_loop H 3509 (by norm_num)
  have hD : ∀ k < 3510, ap T.pts k < 3510 := fun k hk => by
    rw [H.pts k hk]
    exact H.plt k hk
  have hd : ∀ i < 3510, ∀ j < i, ap T.pts j ≠ ap T.pts i := fun i hi j hj e => by
    rw [H.pts j (by omega), H.pts i hi] at e
    have := congrArg POS e
    rw [H.pos j (by omega), H.pos i hi] at this
    omega
  have hl := set_loopV (N := 3510) (v0 := (0 : UInt32)) (D := fun k => ap T.pts k)
    (v := fun k => UInt32.ofNat
      ((List.range' 1 3509).foldl (fun im k => im.set! k (ap tc[ap T.lab k]! im[ap T.par k]!))
        ((Array.replicate 3510 0).set! 0 (UI 0)))[k]!) (m := 3510) hD hd
  rw [recon_eq H, ← H.pts k hk, ap_eq_of_get (hl.2 k hk), hv k (by omega), UInt32.toNat_ofNat',
    Nat.mod_eq_of_lt (lt_trans (H.vlt k hk) (by norm_num))]

theorem surj_of (H : RecHyp T tc P PA LB POS V) : ∀ i < 3510, ∃ k < 3510, P k = i := by
  intro i hi
  have hinj : Function.Injective fun k : Fin 3510 => (⟨P k.val, H.plt k.val k.2⟩ : Fin 3510) := by
    intro a b e
    have e' : P a.val = P b.val := congrArg Fin.val e
    have := congrArg POS e'
    rw [H.pos a.val a.2, H.pos b.val b.2] at this
    exact Fin.ext this
  obtain ⟨k, hk⟩ := (Finite.injective_iff_surjective.1 hinj) ⟨i, hi⟩
  exact ⟨k.val, k.2, congrArg Fin.val hk⟩

end Recon

theorem rec_hyp : RecHyp F6 tcN (r32 (PTSN 6)) (r32 (PARN 6)) (r32 (LABN 6)) (r32 (POSN 6))
    fun k => UK (r32 (PTSN 6) k) := by
  have c6 := cnts.2.2.2.2.2
  have hk6 : ∀ k < 3510, k < CNTN 6 := fun k hk => by rw [c6]; exact hk
  refine ⟨?_, fun k hk => ap_pts (hk6 k hk), fun k hk => ap_par (hk6 k hk),
    fun k hk => ap_lab (hk6 k hk), fun k hk => pts_lt (by norm_num) (by norm_num) (hk6 k hk),
    fun k hk => (pt_spec (pt_all (i := 6) (by norm_num) (by norm_num) k (hk6 k hk))).pos,
    fun k h0 hk => rec_facts h0 hk, rec_root,
    fun k hk => (uk_facts (pts_lt (i := 6) (by norm_num) (by norm_num) (hk6 k hk))).1,
    fun l hl => tc_get hl⟩
  change (Array.ofFn (n := CNTN 6) fun k => UInt32.ofNat (r32 (PTSN 6) k.val)).size = 3510
  rw [Array.size_ofFn, c6]

theorem recon_ap : ∀ i < 3510, ap (reconTab F6 tcN uImg[0]!) i = UK i := by
  intro i hi
  obtain ⟨k, hk, rfl⟩ := surj_of rec_hyp i hi
  rw [(ui_get (l := 0) (by norm_num)).1]
  exact recon_pt rec_hyp hk

theorem U_ap {i : Nat} (hi : i < 3510) :
    ap (reconTab (closTree tbN 6) tcN uImg[0]!) i = UK i := by
  rw [(clos_eq (i := 6) (by norm_num) (by norm_num)).1]
  exact recon_ap i hi

theorem compT_size (P Q : Table) : (compT 3510 P Q).size = 3510 := by simp [compT]

theorem uConj_get {j : Nat} (hj : j < 6) {x : Nat} (hx : x < 3510) :
    UK (cK (NB j) (UK x)) = cK (UI j) x := by
  have h := Raw.Orb.allN_iff.1 (uConjAll j hj) x hx
  rw [Nat.beq_eq] at h
  exact h

theorem conj_tab {j : Nat} (hj : j < 6) :
    compT 3510 (reconTab (closTree tbN 6) tcN uImg[0]!)
      (compT 3510 tbN[j]! (reconTab (closTree tbN 6) tcN uImg[0]!)) = tcN[j]! := by
  have hT1 : TR 3510 (compT 3510 (reconTab (closTree tbN 6) tcN uImg[0]!)
      (compT 3510 tbN[j]! (reconTab (closTree tbN 6) tcN uImg[0]!))) (cK (UI j)) := by
    refine ⟨compT_size _ _, fun x hx => ?_⟩
    have u1 := uk_facts hx
    have hc := cK_lt (NB j) u1.1
    rw [ap_compT' _ _ hx, ap_compT' _ _ hx, U_ap hx, tb_get hj _ u1.1, LC, U_ap hc,
      uConj_get hj hx]
    exact ⟨rfl, cK_lt _ hx⟩
  have hT2 : TR 3510 tcN[j]! (cK (UI j)) := by
    refine ⟨?_, fun x hx => ⟨tc_get hj x hx, cK_lt _ hx⟩⟩
    rw [getElem!_pos _ j (by rw [Array.size_map, uImg_size]; exact hj), Array.getElem_map]
    exact cTab_size _
  exact CFSG.KS.Fi22L.TR_ext hT1 hT2

theorem sift_ok {j : Nat} (hj : j < 11) :
    sift (chainTrees 3510 LSN sylBase) LSN sylQb chainQ 0
      (apT (compT 3510 (reconTab (closTree tbN 6) tcN uImg[0]!)
        (compT 3510 LSN[2 * j]! (reconTab (closTree tbN 6) tcN uImg[0]!))) chainQ) = true := by
  have hval : ∀ q < 3510, ap (compT 3510 (reconTab (closTree tbN 6) tcN uImg[0]!)
      (compT 3510 LSN[2 * j]! (reconTab (closTree tbN 6) tcN uImg[0]!))) q =
        UK (LSK (2 * j) (UK q)) ∧ UK (LSK (2 * j) (UK q)) < 3510 := by
    intro q hq
    have u1 := uk_facts hq
    have hL := (letters_TR (l := 2 * j) (by omega)).2 _ u1.1
    rw [ap_compT' _ _ hq, ap_compT' _ _ hq, U_ap hq, hL.1, U_ap hL.2]
    exact ⟨rfl, (uk_facts hL.2).1⟩
  generalize hP : compT 3510 (reconTab (closTree tbN 6) tcN uImg[0]!)
    (compT 3510 LSN[2 * j]! (reconTab (closTree tbN 6) tcN uImg[0]!)) = P at hval
  have hb : ∀ x ∈ apT P chainQ, x < 3510 := fun x hx => by
    rw [apT_map] at hx
    obtain ⟨q, hq, rfl⟩ := Array.mem_map.1 hx
    rw [(hval q (Q_lt chain_hyp q hq)).1]
    exact (hval q (Q_lt chain_hyp q hq)).2
  have hs := sift_eq chain_hyp 2 0 rfl (apT P chainQ) hb
  have ht : chainTrees 3510 LSN sylBase = trees 3510 2 CNTS PTSS POSS PARS LABS :=
    chainTrees_eq chain_hyp
  rw [ht, hs, apT_map, Array.toList_map, chain_hyp.chk.1]
  have e : QL.map (ap P) = QL.map fun q => UK (LSK (2 * j) (UK q)) :=
    List.map_congr_left fun q hq => (hval q (QL_lt q hq)).1
  rw [e]
  have h := Raw.Orb.allN_iff.1 uSift_ok j hj
  unfold siftK at h
  rw [mapK_eq] at h
  exact h

theorem hasFix_spec {F : Nat → Nat} (h : hasFix F = true) : ∃ x < 3510, F x = x := by
  unfold hasFix at h
  rw [Raw.Orb.bIf_eq] at h
  by_cases ha : allN 3510 (fun x => bIf(Nat.beq (F x) x, false, true)) = true
  · rw [ite_eq_left ha] at h
    exact absurd h (by decide)
  · rw [Raw.Orb.allN_iff] at ha
    simp only [not_forall] at ha
    obtain ⟨x, hx, hne⟩ := ha
    refine ⟨x, hx, ?_⟩
    rw [Raw.Orb.bIf_eq] at hne
    by_contra e
    rw [ite_eq_right (fun hb => e (Nat.eq_of_beq_eq_true hb))] at hne
    exact hne rfl

theorem invFix_of {f F : Nat → Nat} (hf : ∀ x < 3510, f x = F x) (hF : ∀ x < 3510, F x < 3510)
    (h : invFixK F = true) : invFix f = true := by
  unfold invFixK at h
  rw [Raw.Orb.bIf_eq] at h
  unfold invFix
  rw [Bool.or_eq_true, Bool.not_eq_true', Bool.not_eq_true']
  split_ifs at h with h1
  · obtain ⟨q, hq, hne⟩ := anyMv_spec h1
    have hq' := QL_lt q hq
    refine Or.inl (not_allIn hq' ?_)
    rw [hf q hq', hf _ (hF q hq')]
    unfold KernelFi22S.sq at hne
    rw [Raw.Orb.strictN_eq] at hne
    simpa using hne
  · obtain ⟨x, hx, e⟩ := hasFix_spec h
    refine Or.inr (not_allIn hx ?_)
    rw [hf x hx, e]
    simp

theorem nfpLeafK_of {k j : Nat} (hk : k < 1024) (hj : j < 128) : nfpLeafK k j = true := by
  have hs : k / 8 < 128 := by omega
  have h := nfpAll (k / 8) hs
  unfold nfpSl at h
  have h' := Raw.Orb.allN_iff.1 h (k % 8) (Nat.mod_lt _ (by norm_num))
  rw [Raw.Orb.strictB_eq] at h'
  have e : Nat.add (Nat.mul (k / 8) 8) (k % 8) = k := Nat.div_add_mod' k 8
  rw [e] at h'
  exact Raw.Orb.allN_iff.1 h' j hj

theorem ab_eq {k j : Nat} (hk : k < 1024) (hj : j < 128) :
    ∀ x < 3510, ap (tabK 0)[k]! (ap (tabK 1)[j]! x) = gK k j x := by
  obtain ⟨c0, c1⟩ := KernelFi22S.cnts
  intro x hx
  have t1 := (tab_TR (i := 1) (by norm_num) (by rw [c1]; exact hj)).2 x hx
  rw [t1.1, ((tab_TR (i := 0) (by norm_num) (by rw [c0]; exact hk)).2 _ t1.2).1]
  unfold gK
  rw [Raw.Orb.strictN_eq]

theorem leafNfp_ok {k j : Nat} (hk : k < 1024) (hj : j < 128) :
    leafNfp (tabK 0)[k]! (tabK 1)[j]! (reconTab (closTree tbN 6) tcN uImg[0]!) = true := by
  have hAB := ab_eq hk hj
  have hG := inJ_gK hk hj
  have hl := nfpLeafK_of hk hj
  unfold nfpLeafK at hl
  simp only [Raw.Orb.bAnd_eq, Bool.and_eq_true] at hl
  obtain ⟨l1, l2, l3⟩ := hl
  have hGU : ∀ x < 3510, gU k j x = gK k j (UK x) := fun x _ => Raw.Orb.strictN_eq _ _
  have hGUlt : ∀ x < 3510, gU k j x < 3510 := fun x hx => by
    rw [hGU x hx]
    exact hG.lt (uk_facts hx).1
  have hf : ∀ x < 3510, ap (tabK 0)[k]! (ap (tabK 1)[j]!
      (ap (reconTab (closTree tbN 6) tcN uImg[0]!) x)) = gU k j x := fun x hx => by
    rw [U_ap hx, hAB _ (uk_facts hx).1, hGU x hx]
  unfold leafNfp
  simp only [Bool.and_eq_true, Bool.not_eq_true']
  refine ⟨⟨invFix_of hAB (fun x hx => hG.lt hx) l1, ?_⟩, invFix_of hf hGUlt l3⟩
  obtain ⟨q, hq, hne⟩ := anyMv_spec l2
  have hq' := QL_lt q hq
  refine not_allIn hq' ?_
  rw [hf q hq']
  simpa using hne

theorem nfp_ok : nfpChecks orbL 3 = true := by
  obtain ⟨c0, c1⟩ := KernelFi22S.cnts
  have c6 := cnts.2.2.2.2.2
  unfold nfpChecks
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [CFSG.Sporadic.Th.allIn_eq_true]
    intro i hi1 hi
    exact (clos_eq hi1 hi).2
  · rw [(clos_eq (i := 6) (by norm_num) (by norm_num)).1]
    simp [tbfsRec, c6]
  · rw [CFSG.Sporadic.Th.allIn_eq_true]
    intro i hi1 hi
    rw [beq_iff_eq, cand_eq hi1 hi, bounds_get hi]
    have h := candNAll i hi1 hi
    unfold candN at h
    exact Nat.eq_of_beq_eq_true h
  · rw [TW.allIn_iff]
    intro i hi
    rw [decide_eq_true_eq, U_ap hi]
    exact (uk_facts hi).1
  · unfold CFSG.Sporadic.Th.Native.invoOK
    rw [TW.allIn_iff]
    intro i hi
    rw [U_ap hi, U_ap (uk_facts hi).1, (uk_facts hi).2, beq_self_eq_true]
  · rw [TW.allIn_iff]
    intro j hj
    obtain ⟨e1, hb⟩ := nb_get hj
    rw [e1, U_ap hb, (ui_get hj).1, beq_iff_eq]
    exact Nat.eq_of_beq_eq_true (Raw.Orb.allN_iff.1 uBase_ok j hj)
  · rw [TW.allIn_iff]
    intro j hj
    rw [beq_iff_eq]
    exact conj_tab hj
  · rw [TW.allIn_iff]
    intro j hj
    exact sift_ok (j := j) hj
  · apply parAll_of
    intro k hk
    change k < (tabK 0).size at hk
    rw [tabK_size (by norm_num), c0] at hk
    rw [Array.all_eq_true]
    intro j hj
    change j < (tabK 1).size at hj
    have hj' := hj
    rw [tabK_size (by norm_num), c1] at hj'
    rw [← getElem!_pos (tabK 1) j hj]
    exact leafNfp_ok hk hj'

end CertificateChecks.KernelFi22N

end
