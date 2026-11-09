module

public import Certificates.Kernel.SporSch.Pair.J2Check
public import CFSG.Certificates.Kernel.SporSch.Cnt3Proof
public import CFSG.Certificates.Kernel.SporSch.PairClProof
public import Certificates.Kernel.SporSch.Pair.J2FibGrp
import CFSG.Certificates.Kernel.SporSch.TabSum

public section

namespace CertificateChecks.KernelSporSch.PJ2Facts

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative CFSG.Sporadic.Schreier.PairJ2
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.PJ2W
open CertificateChecks.KernelSporSch.PJ2Check

theorem stepM_eq (a0 b0 a1 b1 : Nat) (o2 o3 c0 c1 : Bool) (s : Nat) :
    stepM a0 b0 a1 b1 o2 o3 c0 c1 s =
      s + (nIf(o2, nIf(true, 1048577, 1), 0) + nIf(o3, nIf(c0, b0, a0), 0) +
        nIf(o3, nIf(c1, b1, a1), 0)) := by
  cases o2 <;> cases o3 <;> cases c0 <;> cases c1 <;> simp only [stepM, strictN_val, Nat.add_eq] <;>
    omega

theorem stepM_sum (o2 o3 c0 c1 : Bool) :
    nIf(o2, nIf(true, 1048577, 1), 0) + nIf(o3, nIf(c0, 1152922604118474752, 1099511627776), 0) +
        nIf(o3, nIf(c1, 1267651809154049016125877911552, 1208925819614629174706176), 0) =
      nIf(o2, nIf(true, 1048577, 1), 0) + 1099511627776 * nIf(o3, nIf(c0, 1048577, 1), 0) +
        1208925819614629174706176 * nIf(o3, nIf(c1, 1048577, 1), 0) := by
  cases o2 <;> cases o3 <;> cases c0 <;> cases c1 <;> rfl

theorem ordPre_eq (w : Nat) (bs W : List Nat) (m : Nat) (hbs : bs ≠ []) :
    bAnd(Nat.beq (evPowK w W m (bs.headD 0)) (bs.headD 0), ordB0 w bs W m) = ordB0 w bs W m := by
  obtain ⟨b, bs', rfl⟩ := List.exists_cons_of_ne_nil hbs
  change bAnd(Nat.beq (evPowK w W m b) b, bAnd(bAnd(Nat.beq (evPowK w W m b) b,
    fixBK w bs' W m), _)) = bAnd(bAnd(Nat.beq (evPowK w W m b) b, fixBK w bs' W m), _)
  cases Nat.beq (evPowK w W m b) b <;> rfl

theorem ord23_eq (w : Nat) (bs W : List Nat) (hbs : bs ≠ []) :
    bAnd(Nat.beq (evPowK w W 2 (bs.headD 0)) (bs.headD 0), ordB0 w bs W 2) = ordB0 w bs W 2 ∧
      bAnd(Nat.beq (evRK w W (evPowK w W 2 (bs.headD 0))) (bs.headD 0), ordB0 w bs W 3) =
        ordB0 w bs W 3 := by
  refine ⟨ordPre_eq w bs W 2 hbs, ?_⟩
  have e : evRK w W (evPowK w W 2 (bs.headD 0)) = evPowK w W 3 (bs.headD 0) :=
    (strictN_val _ _).symm
  rw [e]
  exact ordPre_eq w bs W 3 hbs

theorem patW_ag2 {n : Nat} {x x' y y' : List (Array Nat)} (hx : Cnt3P.WAg n x x')
    (hy : Cnt3P.WAg n y y') : ∀ pat, Cnt3P.WAg n (patW x y pat) (patW x' y' pat)
  | [] => fun _ hp => ⟨rfl, hp⟩
  | b :: pat => by
    rw [Cnt3P.patW_cons, Cnt3P.patW_cons]
    refine (patW_ag2 hx hy pat).append ?_
    cases b
    · exact hx
    · exact hy

theorem condsOK_rep {n : Nat} {x x' y : List (Array Nat)} (hx : Cnt3P.WAg n x x')
    (hy : Cnt3P.WAg n y y) {bs : List Nat} (hbs : ∀ b ∈ bs, b < n)
    (conds : List (List Bool × Nat)) :
    PairNative.condsOK bs x y conds = PairNative.condsOK bs x' y conds := by
  have e : ∀ c : List Bool × Nat, PairNative.ordB bs (patW x y c.1) c.2 =
      PairNative.ordB bs (patW x' y c.1) c.2 := fun c => Cnt3P.ordB_ag (patW_ag2 hx hy c.1) hbs c.2
  unfold PairNative.condsOK
  simp only [e]

theorem condsK_rep {n w : Nat} {bs X X' Y : List Nat} (hX : canonL n w X = true)
    (hX' : canonL n w X' = true)
    (hag : allN n (fun p => Nat.beq (evRK w X p) (evRK w X' p)) = true)
    (hY : Cnt3P.RangeL n w Y) (hbs : ∀ b ∈ bs, b < n) (conds : List (List Bool × Nat)) :
    cnt3.condsK w bs X Y conds = cnt3.condsK w bs X' Y conds := by
  have rX := Cnt3P.rangeL_of_canonL hX
  have rX' := Cnt3P.rangeL_of_canonL hX'
  rw [Cnt3P.condsK_eq rX hY hbs, Cnt3P.condsK_eq rX' hY hbs]
  refine condsOK_rep (fun p hp => ?_) (Cnt3P.rangeL_ag hY) hbs conds
  have e := Nat.eq_of_beq_eq_true (Raw.Orb.allN_iff.1 hag p hp)
  rw [← (Cnt3P.evRK_eq rX p hp).1, ← (Cnt3P.evRK_eq rX' p hp).1]
  exact ⟨e, (Cnt3P.evRK_eq rX p hp).2⟩

theorem cnt3_rep {n w kS BP m : Nat} {PS PSI LR TR TRI : Nat → Nat}
    {S : Array (Array Nat)} {base : Array Nat} {bs X X' : List Nat}
    {conds : List (List Bool × Nat)} (hb : Binds n w PS kS 3 BP S base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS 3 BP) (hbs : base.toList = bs)
    (hX : canonL n w X = true) (hX' : canonL n w X' = true)
    (hag : allN n (fun p => Nat.beq (evRK w X p) (evRK w X' p)) = true) (k0 : Nat)
    (hk0 : k0 < rcnt (LR 0)) :
    cnt3 n w LR TR bs m X conds k0 = cnt3 n w LR TR bs m X' conds k0 := by
  have hbsl : ∀ b ∈ bs, b < n := by
    intro b hb'
    rw [← hbs, Array.mem_toList_iff] at hb'
    obtain ⟨t, ht, rfl⟩ := Array.mem_iff_getElem.1 hb'
    have ht3 : t < 3 := by rw [← hb.2.2.2.2.2.1]; exact ht
    have := Cnt3P.base_lt3 hb hl t ht3
    rwa [getElem!_pos base t ht] at this
  rw [Cnt3P.cnt3_eq, Cnt3P.cnt3_eq]
  refine Finset.sum_congr rfl fun k1 hk1 => Finset.sum_congr rfl fun k2 hk2 => ?_
  rw [Finset.mem_range] at hk1 hk2
  have hK : Cnt3P.RangeL n w [trK n (Nat.mul n w) LR TR 2 k2, trK n (Nat.mul n w) LR TR 1 k1,
      trK n (Nat.mul n w) LR TR 0 k0] := by
    intro W hW q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hW
    rcases hW with rfl | rfl | rfl
    · exact ((Cnt3P.lev_agree hb hp hl (i := 2) (by norm_num)).2 k2 hk2 q hq).2
    · exact ((Cnt3P.lev_agree hb hp hl (i := 1) (by norm_num)).2 k1 hk1 q hq).2
    · exact ((Cnt3P.lev_agree hb hp hl (i := 0) (by norm_num)).2 k0 hk0 q hq).2
  unfold Cnt3P.vv
  rw [condsK_rep hX hX' hag hK hbsl conds]

theorem pow2_base (w b t0 t1 t2 : Nat) (h1 : pg w (mask w) t1 b = b)
    (h2 : pg w (mask w) t2 b = b) :
    evRK w [t1, t0] (pg w (mask w) t2 (pg w (mask w) t0 b)) = evPowK w [t2, t1, t0] 2 b := by
  have e3 : ∀ p, evRK w [t2, t1, t0] p =
      pg w (mask w) t0 (pg w (mask w) t1 (pg w (mask w) t2 p)) := fun p => by
    change strictN (pg w (mask w) t2 p) (fun p => strictN (pg w (mask w) t1 p)
      (fun p => strictN (pg w (mask w) t0 p) (fun p => p))) = _
    simp only [strictN_val]
  have e2 : evRK w [t1, t0] (pg w (mask w) t2 (pg w (mask w) t0 b)) =
      pg w (mask w) t0 (pg w (mask w) t1 (pg w (mask w) t2 (pg w (mask w) t0 b))) := by
    change strictN (pg w (mask w) t1 _) (fun p => strictN (pg w (mask w) t0 p) (fun p => p)) = _
    simp only [strictN_val]
  have ep : evPowK w [t2, t1, t0] 2 b =
      evRK w [t2, t1, t0] (evRK w [t2, t1, t0] b) := by
    change strictN (strictN b (evRK w [t2, t1, t0])) (evRK w [t2, t1, t0]) = _
    simp only [strictN_val]
  rw [ep, e3 b, h2, h1, e3, e2]

theorem foldT_eq (L : List Nat) (f : Nat → Nat → Nat) (s : Nat) :
    foldT L f s = L.foldl (fun s t => f t s) s := by
  induction L generalizing s with
  | nil => rfl
  | cons t L ih => exact (strictN_val _ _).trans (ih _)

theorem foldT_map (m : Nat) (g : Nat → Nat) (f : Nat → Nat → Nat) (s : Nat) :
    foldT ((List.range m).map g) f s = foldUp m (fun k s => f (g k) s) s := by
  rw [foldT_eq, List.foldl_map, Raw.Orb.foldUp_eq]

theorem cntM_eq (n w : Nat) (LR TR : Nat → Nat) (bs T1 : List Nat) (x0 x1 : Nat) (k0 : Nat)
    (hbs : bs ≠ [])
    (hT1 : T1 = (List.range (rcnt (LR 1))).map (trK n (Nat.mul n w) LR TR 1))
    (hf1 : ∀ k < rcnt (LR 1), pg w (mask w) (trK n (Nat.mul n w) LR TR 1 k) (bs.headD 0) =
      bs.headD 0)
    (hf2 : ∀ k < rcnt (LR 2), pg w (mask w) (trK n (Nat.mul n w) LR TR 2 k) (bs.headD 0) =
      bs.headD 0) :
    cntM n w LR TR bs T1 x0 x1 k0 = cnt3 n w LR TR bs 2 [] [] k0 +
      1099511627776 * cnt3 n w LR TR bs 3 [x0] conds k0 +
      1208925819614629174706176 * cnt3 n w LR TR bs 3 [x1] conds k0 := by
  rw [Cnt3P.cnt3_eq, Cnt3P.cnt3_eq, Cnt3P.cnt3_eq, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  unfold cntM
  simp only [strictN_val, hT1, foldT_map]
  refine (Tab.foldUp_add _ (fun k2 hk2 s => ?_) 0).trans (Nat.zero_add _)
  exact Tab.foldUp_add (fun k1 => Cnt3P.vv n w LR TR bs 2 [] [] k0 k1 k2 +
      1099511627776 * Cnt3P.vv n w LR TR bs 3 [x0] conds k0 k1 k2 +
      1208925819614629174706176 * Cnt3P.vv n w LR TR bs 3 [x1] conds k0 k1 k2)
    (fun k1 hk1 s => by
      rw [pow2_base w _ _ _ _ (hf1 k1 hk1) (hf2 k2 hk2), (ord23_eq w bs _ hbs).1,
        (ord23_eq w bs _ hbs).2, stepM_eq, stepM_sum]
      rfl) s

theorem sumN_eq_sum (m : Nat) (f : Nat → Nat) : sumN m f = ∑ k ∈ Finset.range m, f k := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change strictN (sumN m f) (fun a => Nat.add (f m) a) = _
    rw [strictN_val, ih, Finset.sum_range_succ, Nat.add_eq, Nat.add_comm]

theorem dsum_le (r1 r2 : Nat) (g : Nat → Nat → Nat) (hg : ∀ a b, g a b ≤ 1) :
    ∑ k1 ∈ Finset.range r1, ∑ k2 ∈ Finset.range r2, g k1 k2 ≤ r1 * r2 :=
  (Finset.sum_le_sum fun k1 _ => Finset.sum_le_sum fun k2 _ => hg k1 k2).trans (by simp)

theorem cnt3_parts (n w : Nat) (LR TR : Nat → Nat) (bs : List Nat) (m : Nat) (XP : List Nat)
    (conds : List (List Bool × Nat)) (k0 : Nat) : ∃ A B,
      cnt3 n w LR TR bs m XP conds k0 = A + 1048576 * B ∧ A ≤ rcnt (LR 1) * rcnt (LR 2) ∧
        B ≤ rcnt (LR 1) * rcnt (LR 2) := by
  rw [Cnt3P.cnt3_eq]
  simp only [Cnt3P.vv_split, Finset.sum_add_distrib, ← Finset.mul_sum]
  exact ⟨_, _, rfl, dsum_le _ _ _ fun a b => by split <;> omega,
    dsum_le _ _ _ fun a b => by split <;> omega⟩

section Orb

open CertificateChecks.KernelSporSch.PJ2Fib CertificateChecks.KernelSporSch.PJ2Orb
open CFSG.KS.SporSch.FibOrb Finset

theorem mvK {j : Nat} (hj : j < 33) :
    cntM 315 9 PJ2.LR PJ2.TR bs T1 U Z (KJ j) = MV.getD j 0 := by
  rcases (by omega : j < 9 ∨ (9 ≤ j ∧ j < 18) ∨ (18 ≤ j ∧ j < 26) ∨ 26 ≤ j) with
    h | ⟨h, h'⟩ | ⟨h, h'⟩ | h
  · have e := Nat.eq_of_beq_eq_true (allN_spec mv0 j h)
    rw [Nat.add_eq, Nat.zero_add] at e
    exact e
  · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le h
    have e := Nat.eq_of_beq_eq_true (allN_spec mv1 i (by omega))
    rw [Nat.add_eq] at e
    exact e
  · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le h
    have e := Nat.eq_of_beq_eq_true (allN_spec mv2 i (by omega))
    rw [Nat.add_eq] at e
    exact e
  · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le h
    have e := Nat.eq_of_beq_eq_true (allN_spec mv3 i (by omega))
    rw [Nat.add_eq] at e
    exact e

theorem fld {j : Nat} (hj : j < 33) :
    cnt3 315 9 PJ2.LR PJ2.TR bs 2 [] [] (KJ j) % 1048576 = MV.getD j 0 / 1 % 1048576 ∧
      cnt3 315 9 PJ2.LR PJ2.TR bs 3 [U] conds (KJ j) % 1048576 =
        MV.getD j 0 / 1099511627776 % 1048576 ∧
      cnt3 315 9 PJ2.LR PJ2.TR bs 3 [U] conds (KJ j) / 1048576 =
        MV.getD j 0 / 1152921504606846976 % 1048576 ∧
      cnt3 315 9 PJ2.LR PJ2.TR bs 3 [Z] conds (KJ j) / 1048576 =
        MV.getD j 0 / 1267650600228229401496703205376 % 1048576 := by
  have e := mvK hj
  rw [cntM_eq 315 9 PJ2.LR PJ2.TR bs T1 U Z (KJ j) (List.cons_ne_nil _ _) t1_eq
    (fun k hk => Nat.eq_of_beq_eq_true (allN_spec fixL1 k hk))
    (fun k hk => Nat.eq_of_beq_eq_true (allN_spec fixL2 k hk))] at e
  obtain ⟨a2, b2, e2, ha2, hb2⟩ := cnt3_parts 315 9 PJ2.LR PJ2.TR bs 2 [] [] (KJ j)
  obtain ⟨a3, b3, e3, ha3, hb3⟩ := cnt3_parts 315 9 PJ2.LR PJ2.TR bs 3 [U] conds (KJ j)
  obtain ⟨a4, b4, e4, ha4, hb4⟩ := cnt3_parts 315 9 PJ2.LR PJ2.TR bs 3 [Z] conds (KJ j)
  rw [Nat.eq_of_beq_eq_true hr12] at ha2 hb2 ha3 hb3 ha4 hb4
  rw [e2, e3, e4] at e
  rw [e2, e3, e4]
  omega

theorem fsum (s : Nat) (G : Nat → Nat)
    (hG : ∀ j < 33, G (KJ j) = Nat.mod (Nat.div (MV.getD j 0) s) 1048576)
    (hfor : ∑ k ∈ range 315, G k = ∑ j ∈ range 33,
      #((range 315).filter fun a => pg 9 (mask 9) OJP a = j) * G (KJ j)) {H : Nat → Nat} {T : Nat}
    (hT : sumN 315 H = T)
    (hH : ∀ a, H a = Nat.mod (Nat.div (MV.getD (pg 9 (mask 9) OJP a) 0) s) 1048576) :
    ∑ k ∈ range 315, G k = T := by
  have eH : H = fun a => Nat.mod (Nat.div (MV.getD (pg 9 (mask 9) OJP a) 0) s) 1048576 :=
    funext hH
  rw [eH] at hT
  have h2 : (∑ j ∈ range 33, #((range 315).filter fun a => pg 9 (mask 9) OJP a = j) * G (KJ j)) =
      ∑ j ∈ range 33, #((range 315).filter fun a => pg 9 (mask 9) OJP a = j) *
        Nat.mod (Nat.div (MV.getD j 0) s) 1048576 :=
    Finset.sum_congr rfl fun j hj => by rw [hG j (mem_range.1 hj)]
  rw [hfor, h2, sum_cls_card (fun j => Nat.mod (Nat.div (MV.getD j 0) s) 1048576)
    (fun a => pg 9 (mask 9) OJP a) fun a ha => (forest_at ha).1, ← sumN_eq_sum]
  exact hT

theorem hst (a : Nat) (ha : a < 315) (hd : pg 9 (mask 9) DEP a ≠ 0) :
    pg 9 (mask 9) PAR a < 315 ∧ pg 9 (mask 9) OJP (pg 9 (mask 9) PAR a) = pg 9 (mask 9) OJP a ∧
      pg 9 (mask 9) DEP (pg 9 (mask 9) PAR a) + 1 = pg 9 (mask 9) DEP a ∧
      hs (pg 9 (mask 9) GIP a) (pt (pg 9 (mask 9) PAR a)) = pt a := by
  obtain ⟨p1, p2, p3, p4, p5⟩ := (forest_at ha).2.2 hd
  exact ⟨p1, p2, p3, hs_edge ha p4 p1 p5⟩

theorem conds_pos : ∀ c ∈ conds, 0 < c.2 := by decide

theorem totJ2 :
    sumN 315 (fun k => Nat.mod (cnt3 315 9 PJ2.LR PJ2.TR bs 2 [] [] k) 1048576) = 2835 ∧
      sumN 315 (fun k => Nat.mod (cnt3 315 9 PJ2.LR PJ2.TR bs 3 RP0 conds k) 1048576) = 17360 ∧
      sumN 315 (fun k => Nat.div (cnt3 315 9 PJ2.LR PJ2.TR bs 3 RP0 conds k) 1048576) = 480 ∧
      sumN 315 (fun k => Nat.div (cnt3 315 9 PJ2.LR PJ2.TR bs 3 RQ1 conds k) 1048576) = 0 := by
  have hJ : ∀ a < 315, pg 9 (mask 9) OJP a < 33 := fun a ha => (forest_at ha).1
  have h0 : ∀ a < 315, pg 9 (mask 9) DEP a = 0 → pg 9 (mask 9) RTP (pg 9 (mask 9) OJP a) = a :=
    fun a ha => (forest_at ha).2.1
  have hK : ∀ j < 33, KJ j < 315 ∧ img (KJ j) = pg 9 (mask 9) RTP j := fun j hj => KJ_spec hj
  have h3 : (0 : Nat) < 3 := by norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [sumN_eq_sum]
    have hf := sum_mod_forest (m := 2) (by norm_num) canonNil [] hs hs_mem hs_one
      (fun a => pg 9 (mask 9) OJP a) (fun j => pg 9 (mask 9) RTP j)
      (fun a => pg 9 (mask 9) PAR a) (fun a => pg 9 (mask 9) GIP a)
      (fun a => pg 9 (mask 9) DEP a) KJ hJ h0 hst hK
    have hG : ∀ j < 33, Nat.mod (cnt3 315 9 PJ2.LR PJ2.TR bs 2 [] [] (KJ j)) 1048576 =
        Nat.mod (Nat.div (MV.getD j 0) 1) 1048576 := fun j hj => (fld hj).1
    have hT := Nat.eq_of_beq_eq_true ms0
    exact fsum 1 _ hG hf hT fun _ => rfl
  · rw [sumN_eq_sum]
    have hf := sum_mod_forest h3 canon0 conds hs hs_mem hs_one
      (fun a => pg 9 (mask 9) OJP a) (fun j => pg 9 (mask 9) RTP j)
      (fun a => pg 9 (mask 9) PAR a) (fun a => pg 9 (mask 9) GIP a)
      (fun a => pg 9 (mask 9) DEP a) KJ hJ h0 hst hK
    have hG : ∀ j < 33, Nat.mod (cnt3 315 9 PJ2.LR PJ2.TR bs 3 RP0 conds (KJ j)) 1048576 =
        Nat.mod (Nat.div (MV.getD j 0) 1099511627776) 1048576 := fun j hj =>
      ((cnt3_mod h3 canon0 conds (KJ_spec hj).1).trans
        (cnt3_mod h3 canonU conds (KJ_spec hj).1).symm).trans (fld hj).2.1
    have hT := Nat.eq_of_beq_eq_true ms2
    exact fsum 1099511627776 _ hG hf hT fun _ => rfl
  · rw [sumN_eq_sum, sum_div_conj h3 canon0 canonU (xg := spW UM) (cg := (spW UA)⁻¹) rp0_rep
      (by rw [← uG_conj]; exact uG_rep) (spW_mem _ (by decide))
      (j2Chain.originalSubgroup.inv_mem (spW_mem _ (by decide))) conds_pos]
    have hf := sum_div_forest h3 canonU uG_rep uG_mem conds_pos hs hs_mem hs_one hs_comU
      (fun a => pg 9 (mask 9) OJP a) (fun j => pg 9 (mask 9) RTP j)
      (fun a => pg 9 (mask 9) PAR a) (fun a => pg 9 (mask 9) GIP a)
      (fun a => pg 9 (mask 9) DEP a) KJ hJ h0 hst hK
    have hG : ∀ j < 33, Nat.div (cnt3 315 9 PJ2.LR PJ2.TR bs 3 [U] conds (KJ j)) 1048576 =
        Nat.mod (Nat.div (MV.getD j 0) 1152921504606846976) 1048576 := fun j hj =>
      (fld hj).2.2.1
    have hT := Nat.eq_of_beq_eq_true ms3
    exact fsum 1152921504606846976 _ hG hf hT fun _ => rfl
  · rw [sumN_eq_sum, sum_div_conj h3 canonQ1 canonZ (xg := spW ZM) (cg := (spW ZA)⁻¹) rq1_rep
      (by rw [← zG_conj]; exact zG_rep) (spW_mem _ (by decide))
      (j2Chain.originalSubgroup.inv_mem (spW_mem _ (by decide))) conds_pos]
    have hf := sum_div_forest h3 canonZ zG_rep zG_mem conds_pos hs hs_mem hs_one hs_comZ
      (fun a => pg 9 (mask 9) OJP a) (fun j => pg 9 (mask 9) RTP j)
      (fun a => pg 9 (mask 9) PAR a) (fun a => pg 9 (mask 9) GIP a)
      (fun a => pg 9 (mask 9) DEP a) KJ hJ h0 hst hK
    have hG : ∀ j < 33, Nat.div (cnt3 315 9 PJ2.LR PJ2.TR bs 3 [Z] conds (KJ j)) 1048576 =
        Nat.mod (Nat.div (MV.getD j 0) 1267650600228229401496703205376) 1048576 := fun j hj =>
      (fld hj).2.2.2
    have hT := Nat.eq_of_beq_eq_true ms5
    exact fsum 1267650600228229401496703205376 _ hG hf hT fun _ => rfl

end Orb

private theorem sum_two {w₀ w₁ : List (Array Nat)}
    {C₀ C₁ : Array (Array Nat) × Array Nat × Array Nat} {s : Nat}
    (h : C₀.1.size + C₁.1.size = s) : ([(w₀, C₀), (w₁, C₁)].map fun c => c.2.1.size).sum = s := by
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
  exact h

private theorem wsum_two {w₀ w₁ : List (Array Nat)}
    {C₀ C₁ : Array (Array Nat) × Array Nat × Array Nat} {f : List (Array Nat) → Nat}
    {n₀ n₁ t : Nat} (e₀ : f w₀ = n₀) (e₁ : f w₁ = n₁) (h : C₀.1.size * n₀ + C₁.1.size * n₁ = t) :
    ([(w₀, C₀), (w₁, C₁)].map fun c => c.2.1.size * f c.1).sum = t := by
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
  rw [e₀, e₁]
  exact h

theorem wtot (x0 x1 : Nat) :
    x0 * countW (fun y => ordB bs y 3 && condsOK bs wA y conds) blocks [] +
      x1 * countW (fun y => ordB bs y 3 &&
        condsOK bs (List.replicate 6 (patW wA wB commPat)).flatten y conds) blocks [] =
      x0 * 480 + x1 * 0 := by
  have n30 := cnt3_proved (bs := bs) (CS := cnt3 315 9 PJ2.LR PJ2.TR bs 3 RP0 conds) PJ2.binds
    PJ2.perm PJ2.hl rfl canon0 hsz (fun _ _ => rfl)
  have n31 := cnt3_proved (bs := bs) (m := 3) (XP := RP1)
    (CS := cnt3 315 9 PJ2.LR PJ2.TR bs 3 RQ1 conds) PJ2.binds PJ2.perm PJ2.hl rfl canon1 hsz
    (fun k0 hk0 => cnt3_rep PJ2.binds PJ2.perm PJ2.hl rfl canon1 canonQ1 agQ1 k0 hk0)
  rw [PairJ2.blocks, PairJ2.groups, rep1_eq, rep0_eq, PairJ2.levels, n30.2, n31.2,
    Nat.eq_of_beq_eq_true hr0, totJ2.2.2.1, totJ2.2.2.2]

set_option maxRecDepth 400000 in
theorem facts : (rawChainOK 315 ((j2StrongArrs ()).extract 0 2) (j2StrongArrs ()) baseArr (j2Words ()) 1 =
        true ∧ rawOrbitSizes 315 (j2StrongArrs ()) baseArr = [315, 160, 12])
    ∧ (ordB bs wA 2 = true ∧ ordB bs wB 3 = true ∧ ordB bs (patW wA wB [false, true]) 7 = true ∧
      ordB bs (patW wA wB commPat) 12 = true)
    ∧ (countW (fun w => ordB bs w 2) blocks [] = 2835 ∧
      countW (fun w => ordB bs w 3) blocks [] = 17360)
    ∧ ((∀ c ∈ cl, ordB bs c.1 2 = true) ∧
      (∀ c ∈ cl, closureOK levels bs gens gensInv c.1 c.2.1 c.2.2.1 c.2.2.2 = true) ∧
      keysDistinctNF 315 levels bs (cl.map fun c => c.2.1) = true ∧
      (cl.map fun c => c.2.1.size).sum = 2835)
    ∧ ((cl.map fun c => c.2.1.size *
      countW (fun y => ordB bs y 3 && condsOK bs c.1 y conds) blocks []).sum = 1209600) := by
  have srt := keysK_sound
    (cs := [(PJ2C.c0, nfKeyX 315 9 PJ2.LR PJ2.TR 3 bs PJ2C.XT0 76),
      (PJ2C.c1, nfKeyX 315 9 PJ2.LR PJ2.TR 3 bs PJ2C.XT1 76)]) (by decide) (by decide) PJ2C.hsrt
  have hD := nodup_of_strictInc_mergeSort srt
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at hD
  have cl0 := ClP.closNF_proved (bs := bs) (rep := wA) PJ2.binds PJ2.perm PJ2.hl rfl hg rep0_eq ok0
    (List.nodup_append.1 hD).1
  have cl1 := ClP.closNF_proved (bs := bs) (rep := (List.replicate 6 (patW wA wB commPat)).flatten)
    PJ2.binds PJ2.perm PJ2.hl rfl hg rep1_eq ok1 (List.nodup_append.1 hD).2.1
  have n2 := cnt3_proved (bs := bs) (XP := []) (conds := [])
    (CS := cnt3 315 9 PJ2.LR PJ2.TR bs 2 [] []) PJ2.binds PJ2.perm PJ2.hl rfl canonNil hsz
    (fun _ _ => rfl)
  have n30 := cnt3_proved (bs := bs) (CS := cnt3 315 9 PJ2.LR PJ2.TR bs 3 RP0 conds) PJ2.binds
    PJ2.perm PJ2.hl rfl canon0 hsz (fun _ _ => rfl)
  have h0 := Nat.eq_of_beq_eq_true hr0
  refine ⟨⟨PJ2.chain, PJ2.orbits⟩, PJ2.ords, ⟨?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [PairJ2.blocks, PairJ2.groups, PairJ2.levels, n2.1, h0]
    exact totJ2.1
  · rw [PairJ2.blocks, PairJ2.groups, PairJ2.levels, n30.1, h0]
    exact totJ2.2.1
  · intro c hc
    rw [cl_eq] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · rw [rep0_eq]
      exact ordWK_sound o0
    · rw [rep1_eq]
      exact ordWK_sound o1
  · intro c hc
    rw [cl_eq] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact cl0.1
    · exact cl1.1
  · rw [cl_eq]
    unfold keysDistinctNF
    simp only [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [closureOf, closureOf, PairJ2.levels, cl0.2.2, cl1.2.2]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at srt
    exact srt
  · rw [cl_eq]
    refine sum_two ?_
    rw [closureOf, closureOf, PairJ2.levels, cl0.2.1, cl1.2.1]
    exact Nat.eq_of_beq_eq_true sSz
  · rw [cl_eq]
    refine wsum_two
      (f := fun w => countW (fun y => ordB bs y 3 && condsOK bs w y conds) blocks [])
      (n₀ := countW (fun y => ordB bs y 3 && condsOK bs wA y conds) blocks [])
      (n₁ := countW (fun y => ordB bs y 3 &&
        condsOK bs (List.replicate 6 (patW wA wB commPat)).flatten y conds) blocks []) rfl rfl ?_
    rw [closureOf, closureOf, PairJ2.levels, cl0.2.1, cl1.2.1]
    exact (wtot PJ2C.c0 PJ2C.c1).trans (Nat.eq_of_beq_eq_true sTot)

end CertificateChecks.KernelSporSch.PJ2Facts

end
