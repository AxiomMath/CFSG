module

public import Certificates.Kernel.Sporadic.OddCore.SuzCTK0
public import Certificates.Kernel.Sporadic.OddCore.SuzCTK1
public import Certificates.Kernel.Sporadic.OddCore.SuzCTK2
public import Certificates.Kernel.Sporadic.OddCore.SuzCTK3
public import Certificates.Kernel.Sporadic.OddCore.SuzCTK4
public import Certificates.Kernel.Sporadic.OddCore.SuzCTK5
public import Certificates.Kernel.Sporadic.OddCore.SuzCTO
public import Certificates.Kernel.Sporadic.OddCore.Suz2302
public import Certificates.Kernel.Sporadic.SuzInv.Inner0
public import Certificates.Kernel.Sporadic.SuzInv.Inner1
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue3
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue2
public import Certificates.Kernel.Sporadic.OddCore.Glue
public import CFSG.Certificates.Kernel.Misc.PairCountSound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Sporadic.SmallOddCore.ClassSimple
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzCT

open CFSG.PSL3Four.Native CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum
open CFSG.KC.BfsPin CFSG.Monster.B.Co2.Native CFSG.KS.Mathieu CFSG.KC.Misc.HexAt
open CFSG.Sporadic.SuzOddCore

theorem base_ok : bAnd(szOK 42 6, bAnd(canonK 42 6 (mask 6) (42 * 6) (pidn 42 6),
    bAnd(CFSG.KS.Prim.idK 42 6 (mask 6), bAnd(szOK 54 6,
    bAnd(canonK 54 6 (mask 6) (54 * 6) (pidn 54 6), CFSG.KS.Prim.idK 54 6 (mask 6)))))) = true := by
  quickRfl

theorem fix0_ok : ((List.range 1782).filter fun x =>
    Nat.beq (pg 11 (mask 11) (SuzTP 0) x) x) = fix0L := by decide +kernel

theorem fix1_ok : ((List.range 1782).filter fun x =>
    Nat.beq (pg 11 (mask 11) (SuzTP 1) x) x) = fix1L := by decide +kernel

@[expose] noncomputable def sigK (m : Nat) (L : List Nat) (F G GI : Nat) : Bool :=
  bAnd(canonK m 6 (mask 6) (m * 6) G,
  bAnd(invEqK m 6 (mask 6) (m * 6) G GI,
  bAnd(invEqK m 6 (mask 6) (m * 6) GI G,
  bAnd(canonK m 6 (mask 6) (m * 6) GI,
  bAnd(Nat.beq (pcomp m 6 (mask 6) GI G) (pidn m 6),
    allN m (fun a => Nat.beq (pg 11 (mask 11) F (nget L a)) (nget L (pg 6 (mask 6) G a))))))))

theorem sig0_ok : allN 22 (fun j => sigK 42 fix0L (SuzInvT0.F (Nat.add 32 j)) (K0E.G j) (K0I j)) =
    true := by quickRfl

theorem dg_ok : allN 5 (fun i => bAnd(Nat.beq (DE.G i)
      (pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) (K0E.G 1) (K0E.G (Nat.add i 2)))
        (K0I 1)) (K0I (Nat.add i 2))),
    bAnd(canonK 42 6 (mask 6) (42 * 6) (DE.G i),
    bAnd(invEqK 42 6 (mask 6) (42 * 6) (DE.G i) (DI i),
    bAnd(invEqK 42 6 (mask 6) (42 * 6) (DI i) (DE.G i),
    bAnd(canonK 42 6 (mask 6) (42 * 6) (DI i),
      Nat.beq (pcomp 42 6 (mask 6) (DI i) (DE.G i)) (pidn 42 6))))))) = true := by
  quickRfl

theorem fam_g : allN 5 (fun k => bAnd(Nat.beq (OF.G k) (DE.G k), Nat.beq (OF.GI k) (DI k))) =
    true := by
  quickRfl

theorem heads : bAnd(penumHdK (pidn 42 6) K0E.cnt 40320 K0E.T K0E.PL,
    penumHdK (pidn 42 6) DE.cnt 20160 DE.T DE.PL) = true := by
  quickRfl

theorem orb_hds : allN 10 (fun l =>
    penumHdK (OF.R l) (OF.C l) 5000 (offF OF.T (OF.TO l)) (offF OF.PL (OF.PLO l))) = true := by
  quickRfl

theorem reps_ok : allN 10 (fun l => bAnd(Nat.beq (OF.R l)
    (wordTabK 42 6 (mask 6) (pidn 42 6) DE.G (lget2 classWords l)),
    Nat.beq (OF.C l) (nget classSizes l))) = true := by
  quickRfl

theorem notin : allN 10 (fun l => allN 10 (fun l' => bIf(Nat.beq l l', true,
    allN (OF.C l) (fun q => bIf(Nat.beq (offF OF.T (OF.TO l) q) (OF.R l'), false, true))))) =
    true := by
  quickRfl

theorem d_norm : allN 22 (fun j => allN 5 (fun i =>
    bAnd(strictB (NP1 (Nat.add (Nat.mul j 5) i)) (fun q => bAnd(Nat.blt q DE.cnt,
      Nat.beq (DE.T q) (pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) (K0E.G j) (DE.G i)) (K0I j)))),
    strictB (NP2 (Nat.add (Nat.mul j 5) i)) (fun q => bAnd(Nat.blt q DE.cnt,
      Nat.beq (DE.T q) (pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) (K0I j) (DE.G i))
        (K0E.G j))))))) = true := by
  quickRfl

@[expose] noncomputable def coverK (k : Nat) : Bool :=
  strictB (COV k) (fun wk =>
    strictB (Nat.shiftRight wk 16) (fun l => strictB (Nat.land wk 65535) (fun q =>
      bAnd(Nat.blt l 10, bAnd(Nat.blt q (OF.C l),
        Nat.beq (offF OF.T (OF.TO l) q) (DE.T k))))))

theorem cover0 : allBlk 0 coverK 10080 = true := by quickRfl
theorem cover1 : allBlk 10080 coverK 10080 = true := by quickRfl

theorem base : szOK 42 6 = true ∧ canonK 42 6 (mask 6) (42 * 6) (pidn 42 6) = true ∧
    CFSG.KS.Prim.idK 42 6 (mask 6) = true ∧ szOK 54 6 = true ∧
    canonK 54 6 (mask 6) (54 * 6) (pidn 54 6) = true ∧ CFSG.KS.Prim.idK 54 6 (mask 6) = true := by
  simpa only [bAnd_iff] using base_ok

theorem idTab42 : idTab 42 = unpack 42 6 (pidn 42 6) :=
  (idK_sound base.2.2.1).symm

theorem idTab54 : idTab 54 = unpack 54 6 (pidn 54 6) :=
  (idK_sound base.2.2.2.2.2).symm

theorem comp42 {p q : Nat} (hp : canonK 42 6 (mask 6) (42 * 6) p = true)
    (hq : canonK 42 6 (mask 6) (42 * 6) q = true) :
    comp 42 (unpack 42 6 p) (unpack 42 6 q) = unpack 42 6 (pcomp 42 6 (mask 6) p q) :=
  compA_unpack hp hq

theorem fixList_eq {i : Nat} (hi : i < 4) {L : List Nat}
    (hL : ((List.range 1782).filter fun x => Nat.beq (pg 11 (mask 11) (SuzTP i) x) x) = L) :
    fixList i = L := by
  rw [← hL]
  unfold fixList fixedList
  rw [(CertificateChecks.KernelSpor.OddCore.rep_facts hi).1]
  apply List.filter_congr
  intro x hx
  rw [CFSG.KC.Misc.PairCount.unpack_get (List.mem_range.1 hx)]
  cases h : Nat.beq (pg 11 (mask 11) (SuzTP i) x) x
  · have : pg 11 (mask 11) (SuzTP i) x ≠ x := fun e => by simp [e] at h
    simp [this]
  · simp [Nat.eq_of_beq_eq_true h]

theorem fix_eq0 : fixList 0 = fix0L := fixList_eq (by norm_num) fix0_ok
theorem fix_eq1 : fixList 1 = fix1L := fixList_eq (by norm_num) fix1_ok

theorem sig_facts {m : Nat} {L : List Nat} {F G GI : Nat} (h : sigK m L F G GI = true) :
    canonK m 6 (mask 6) (m * 6) G = true ∧ invEqK m 6 (mask 6) (m * 6) G GI = true ∧
      invEqK m 6 (mask 6) (m * 6) GI G = true ∧ canonK m 6 (mask 6) (m * 6) GI = true ∧
      Nat.beq (pcomp m 6 (mask 6) GI G) (pidn m 6) = true ∧
      allN m (fun a => Nat.beq (pg 11 (mask 11) F (nget L a)) (nget L (pg 6 (mask 6) G a))) =
        true := by
  unfold sigK at h
  simpa only [bAnd_iff] using h

theorem canon_lt {m p a : Nat} (hp : canonK m 6 (mask 6) (m * 6) p = true) (ha : a < m) :
    pg 6 (mask 6) p a < m := by
  unfold canonK at hp
  simp only [bAnd_iff] at hp
  exact Eq.mp Nat.blt_eq (allN_spec hp.2.2 a ha)

theorem restrict_eq {m : Nat} {L : List Nat} {F G GI : Nat} (hm : L.length = m) (hnd : L.Nodup)
    (hlt : ∀ x ∈ L, x < 1782) (h : sigK m L F G GI = true) :
    restrictArr L (unpack 1782 11 F) = unpack m 6 G := by
  obtain ⟨hc, -, -, -, -, hall⟩ := sig_facts h
  apply Array.ext
  · simp [restrictArr, unpack, hm]
  · intro a h1 _
    have ha : a < m := by simpa [restrictArr, hm] using h1
    simp only [restrictArr, List.getElem_toArray, List.getElem_map]
    rw [← getElem!_pos (unpack m 6 G) a (by simp [unpack, ha]),
      CFSG.KC.Misc.PairCount.unpack_get ha]
    have hb := Nat.eq_of_beq_eq_true (allN_spec hall a ha)
    have hs := canon_lt hc ha
    rw [nget_get L (by rw [hm]; exact ha), nget_get L (by rw [hm]; exact hs)] at hb
    rw [CFSG.KC.Misc.PairCount.unpack_get (hlt _ (List.getElem_mem _)), hb,
      hnd.idxOf_getElem]

theorem fix0_facts : fix0L.length = 42 ∧ fix0L.Nodup ∧ ∀ x ∈ fix0L, x < 1782 := by decide +kernel
theorem fix1_facts : fix1L.length = 54 ∧ fix1L.Nodup ∧ ∀ x ∈ fix1L, x < 1782 := by decide +kernel

theorem kgens0_size : (kGens 0).size = 22 := by
  simp [kGens, CertificateChecks.KernelSpor.SuzInv.gensI0.1]

theorem sig0 {j : Nat} (hj : j < 22) :
    sigK 42 fix0L (SuzInvT0.F (Nat.add 32 j)) (K0E.G j) (K0I j) = true :=
  allN_spec sig0_ok j hj

theorem kgens0_get {j : Nat} (hj : j < 22) : (kGens 0)[j]! = unpack 42 6 (K0E.G j) := by
  rw [getElem!_pos (kGens 0) j (by rw [kgens0_size]; exact hj)]
  simp only [kGens, Array.getElem_map]
  rw [← getElem!_pos (invInnerGenArrs 0) j (by simp [CertificateChecks.KernelSpor.SuzInv.gensI0.1]; omega),
    CertificateChecks.KernelSpor.SuzInv.gensI0.2 j hj, fix_eq0]
  exact restrict_eq fix0_facts.1 fix0_facts.2.1 fix0_facts.2.2 (sig0 hj)

theorem kinvs0_get {j : Nat} (hj : j < 22) : (kInvs 0)[j]! = unpack 42 6 (K0I j) := by
  rw [kInvs, getElem!_pos _ j (by simp [kgens0_size]; omega), Array.getElem_map,
    ← getElem!_pos (kGens 0) j (by rw [kgens0_size]; exact hj), kgens0_get hj, fix_eq0,
    fix0_facts.1]
  exact (invEqK_sound (sig_facts (sig0 hj)).2.1).1

theorem k_ok : GensOK 42 6 K0E.k K0E.G (kGens 0) :=
  ⟨by rw [kgens0_size]; rfl, fun _ hj => ⟨kgens0_get hj, (sig_facts (sig0 hj)).1⟩⟩

theorem invsK0 : invsOK 42 (kGens 0) (kInvs 0) = true := by
  unfold invsOK
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨by simp [kInvs], ?_⟩
  unfold allBelow
  rw [all_range_iff]
  intro k hk
  have hk22 : k < 22 := by rwa [kgens0_size] at hk
  obtain ⟨hc, -, -, hci, hpi, -⟩ := sig_facts (sig0 hk22)
  simp only [Bool.and_eq_true, beq_iff_eq]
  rw [kinvs0_get hk22, kgens0_get hk22]
  refine ⟨unpack_size _ _ _, ?_⟩
  rw [comp42 hci hc, idTab42, Nat.eq_of_beq_eq_true hpi]

theorem cover' {L N : Nat} {P : Nat → Prop} (hL : 0 < L)
    (h : ∀ s < N, ∀ i, L * s ≤ i → i < L * s + L → P i) : ∀ i < L * N, P i := by
  intro i hi
  refine h (i / L) (Nat.div_lt_of_lt_mul hi) i (Nat.mul_div_le i L) ?_
  have := Nat.lt_mul_div_succ i hL
  rw [Nat.mul_add, Nat.mul_one] at this
  exact this

theorem part_of {f : Nat → Bool} {b k : Nat} (h : ∀ s < k, f (Nat.add b s) = true) {s : Nat}
    (h1 : b ≤ s) (h2 : s < b + k) : f s = true := by
  have := h (s - b) (by omega)
  rwa [Nat.add_eq, Nat.add_sub_cancel' h1] at this

theorem kSl_all {s : Nat} (hs : s < 90) : kSl s = true := by
  rcases Nat.lt_or_ge s 45 with h1 | h1
  · rcases Nat.lt_or_ge s 15 with h2 | h2
    · exact part_of (f := kSl) (b := 0) (k := 15) (fun s hs => KP0.all s hs) (by omega) (by omega)
    · rcases Nat.lt_or_ge s 30 with h3 | h3
      · exact part_of (f := kSl) (b := 15) (k := 15) (fun s hs => KP1.all s hs) h2 (by omega)
      · exact part_of (f := kSl) (b := 30) (k := 15) (fun s hs => KP2.all s hs) h3 (by omega)
  · rcases Nat.lt_or_ge s 60 with h2 | h2
    · exact part_of (f := kSl) (b := 45) (k := 15) (fun s hs => KP3.all s hs) h1 (by omega)
    · rcases Nat.lt_or_ge s 75 with h3 | h3
      · exact part_of (f := kSl) (b := 60) (k := 15) (fun s hs => KP4.all s hs) h2 (by omega)
      · exact part_of (f := kSl) (b := 75) (k := 15) (fun s hs => KP5.all s hs) h3 (by omega)

theorem kpt_all {i : Nat} (hi : i < K0E.cnt) : penumPtK 42 6 (mask 6) (42 * 6) false K0E.G K0E.GI
    K0E.k K0E.cnt K0E.T K0E.PL K0E.POS K0E.SRT K0E.SRI i = true := by
  have e : K0E.cnt = 40320 := rfl
  have hs : i / 448 < 90 := by omega
  have h1 : 448 * (i / 448) ≤ i := by omega
  have h2 : i < 448 * (i / 448) + 448 := by omega
  exact penumSl_spec (kSl_all hs) i h1 h2 hi

theorem dpt_all {i : Nat} (hi : i < DE.cnt) : penumPtK 42 6 (mask 6) (42 * 6) false DE.G DE.GI
    DE.k DE.cnt DE.T DE.PL DE.POS DE.SRT DE.SRI i = true := by
  have e : DE.cnt = 20160 := rfl
  have hs : i / 2016 < 10 := by omega
  have h1 : 2016 * (i / 2016) ≤ i := by omega
  have h2 : i < 2016 * (i / 2016) + 2016 := by omega
  exact penumSl_spec (DP.all _ hs) i h1 h2 hi

theorem heads' : penumHdK (pidn 42 6) K0E.cnt 40320 K0E.T K0E.PL = true ∧
    penumHdK (pidn 42 6) DE.cnt 20160 DE.T DE.PL = true := by
  simpa only [bAnd_iff] using heads

theorem k_enum : enumOf 42 (kGens 0) 40320 = penumRec 42 6 K0E.cnt K0E.T K0E.PL ∧
    enumOK 42 (kGens 0) (penumRec 42 6 K0E.cnt K0E.T K0E.PL) = true :=
  penumK_left_sound (cap := 40320) base.1 k_ok heads'.1 (fun _ hi => kpt_all hi)

theorem dg_facts {i : Nat} (hi : i < 5) :
    Nat.beq (DE.G i)
      (pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) (K0E.G 1) (K0E.G (Nat.add i 2)))
        (K0I 1)) (K0I (Nat.add i 2))) = true ∧
      canonK 42 6 (mask 6) (42 * 6) (DE.G i) = true ∧
      invEqK 42 6 (mask 6) (42 * 6) (DE.G i) (DI i) = true ∧
      invEqK 42 6 (mask 6) (42 * 6) (DI i) (DE.G i) = true ∧
      canonK 42 6 (mask 6) (42 * 6) (DI i) = true ∧
      Nat.beq (pcomp 42 6 (mask 6) (DI i) (DE.G i)) (pidn 42 6) = true := by
  simpa only [bAnd_iff] using allN_spec dg_ok i hi

theorem dGens_size' : dGens.size = 5 := by simp [dGens]

theorem dgens_get {i : Nat} (hi : i < 5) : dGens[i]! = unpack 42 6 (DE.G i) := by
  rw [dGens, getElem!_pos _ i (by simp; omega), Array.getElem_ofFn,
    Nat.eq_of_beq_eq_true (dg_facts hi).1]
  have c1 := (sig_facts (sig0 (j := 1) (by norm_num))).1
  have c2 := (sig_facts (sig0 (j := i + 2) (by omega))).1
  have c3 := (sig_facts (sig0 (j := 1) (by norm_num))).2.2.2.1
  have c4 := (sig_facts (sig0 (j := i + 2) (by omega))).2.2.2.1
  unfold commTab
  rw [kgens0_get (by norm_num), kgens0_get (by omega), kinvs0_get (by norm_num),
    kinvs0_get (by omega), comp42 c1 c2, comp42 (canonK_pcomp c1 c2) c3,
    comp42 (canonK_pcomp (canonK_pcomp c1 c2) c3) c4]

theorem dinvs_get {i : Nat} (hi : i < 5) : dInvs[i]! = unpack 42 6 (DI i) := by
  rw [dInvs, getElem!_pos _ i (by simp [dGens]; omega), Array.getElem_map,
    ← getElem!_pos dGens i (by rw [dGens_size']; exact hi), dgens_get hi]
  exact (invEqK_sound (dg_facts hi).2.2.1).1

theorem d_ok : GensOK 42 6 DE.k DE.G dGens :=
  ⟨by rw [dGens_size']; rfl, fun _ hi => ⟨dgens_get hi, (dg_facts hi).2.1⟩⟩

theorem d_enum : enumOf 42 dGens 20160 = penumRec 42 6 DE.cnt DE.T DE.PL ∧
    enumOK 42 dGens (penumRec 42 6 DE.cnt DE.T DE.PL) = true :=
  penumK_left_sound (cap := 20160) base.1 d_ok heads'.2 (fun _ hi => dpt_all hi)

theorem normal : normalOK 42 (penumRec 42 6 DE.cnt DE.T DE.PL).tabs (kGens 0) (kInvs 0) dGens =
    true := by
  unfold normalOK
  simp only [Bool.and_eq_true]
  refine ⟨invsK0, ?_⟩
  unfold allBelow
  rw [List.all_eq_true]
  intro j hj
  have hj22 : j < 22 := by simpa [kgens0_size] using List.mem_range.1 hj
  rw [List.all_eq_true]
  intro i hi
  have hi5 : i < 5 := by simpa [dGens_size'] using List.mem_range.1 hi
  have hn := allN_spec (allN_spec d_norm j hj22) i hi5
  obtain ⟨n1, n2⟩ := (bAnd_iff _ _).1 hn
  rw [strictB_app'] at n1 n2
  obtain ⟨q1, e1⟩ := (bAnd_iff _ _).1 n1
  obtain ⟨q2, e2⟩ := (bAnd_iff _ _).1 n2
  obtain ⟨hc, -, -, hci, -, -⟩ := sig_facts (sig0 hj22)
  have hg := d_ok.2 i hi5
  rw [Bool.and_eq_true, kgens0_get hj22, kinvs0_get hj22, hg.1]
  unfold conjTab
  rw [comp42 hc hg.2, comp42 (canonK_pcomp hc hg.2) hci, comp42 hci hg.2,
    comp42 (canonK_pcomp hci hg.2) hc]
  exact ⟨penum_found_sound (fun _ hx => dpt_all hx) (Eq.mp Nat.blt_eq q1)
      (Nat.eq_of_beq_eq_true e1),
    penum_found_sound (fun _ hx => dpt_all hx) (Eq.mp Nat.blt_eq q2) (Nat.eq_of_beq_eq_true e2)⟩

@[expose] noncomputable def orbRec (l : Nat) : Enum :=
  penumRec 42 6 (OF.C l) (offF OF.T (OF.TO l)) (offF OF.PL (OF.PLO l))

theorem orb_pt {l i : Nat} (hl : l < 10) (hi : i < OF.C l) :
    penumPtK 42 6 (mask 6) (42 * 6) true OF.G OF.GI OF.k (OF.C l) (offF OF.T (OF.TO l))
      (offF OF.PL (OF.PLO l)) (offF OF.POS (OF.POSO l)) (offF OF.SRT (OF.SRTO l))
      (offF OF.SRI (OF.SRIO l)) i = true := by
  have hc : OF.C l ≤ 4032 := by interval_cases l <;> decide
  exact penumSl_spec (OP.all l hl) i (Nat.zero_le _) (by omega) hi

theorem fg_ok : GensOK 42 6 OF.k OF.G dGens :=
  ⟨by rw [dGens_size']; rfl, fun j hj => by
    have e := Nat.eq_of_beq_eq_true ((bAnd_iff _ _).1 (allN_spec fam_g j hj)).1
    rw [e]
    exact ⟨dgens_get hj, (dg_facts hj).2.1⟩⟩

theorem fgi_ok : GensOK 42 6 OF.k OF.GI dInvs :=
  ⟨by simp [dInvs, dGens]; rfl, fun j hj => by
    have e := Nat.eq_of_beq_eq_true ((bAnd_iff _ _).1 (allN_spec fam_g j hj)).2
    rw [e]
    exact ⟨dinvs_get hj, (dg_facts hj).2.2.2.2.1⟩⟩

theorem invsD : invsOK 42 dGens dInvs = true := by
  unfold invsOK
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨by simp [dInvs], ?_⟩
  unfold allBelow
  rw [all_range_iff]
  intro k hk
  have hk5 : k < 5 := by simpa [dGens] using hk
  obtain ⟨-, hc, -, -, hci, hpi⟩ := dg_facts hk5
  simp only [Bool.and_eq_true, beq_iff_eq]
  rw [dinvs_get hk5, dgens_get hk5]
  refine ⟨unpack_size _ _ _, ?_⟩
  rw [comp42 hci hc, idTab42, Nat.eq_of_beq_eq_true hpi]

theorem cover_all {k : Nat} (hk : k < 20160) : coverK k = true := by
  rcases Nat.lt_or_ge k 10080 with h0 | h0
  · simpa using allBlk_spec cover0 k h0
  · simpa [Nat.add_sub_cancel' h0] using allBlk_spec cover1 (k - 10080) (by omega)

theorem orb_hd {l : Nat} (hl : l < 10) :
    penumHdK (OF.R l) (OF.C l) 5000 (offF OF.T (OF.TO l)) (offF OF.PL (OF.PLO l)) = true :=
  allN_spec orb_hds l hl

theorem cwords_lt : ∀ l < 10, ∀ j ∈ classWords.getD l [], j < 5 := by decide

theorem rep_eq {l : Nat} (hl : l < 10) : classRep l = unpack 42 6 (OF.R l) := by
  obtain ⟨hr, -⟩ := (bAnd_iff _ _).1 (allN_spec reps_ok l hl)
  rw [Nat.eq_of_beq_eq_true hr, lget2_eq]
  exact (wordTabK_eq idTab42 base.2.1 _ (fun j hj => by
    have hj5 := cwords_lt l hl j hj
    exact ⟨dgens_get hj5, (dg_facts hj5).2.1⟩)).1

theorem orbits_get {l : Nat} (hl : l < 10) :
    classOrbits[l]! = orbitBFS 42 dGens dInvs (classRep l) 5000 := by
  rw [getElem!_pos classOrbits l (by simp [classOrbits]; omega)]
  simp [classOrbits]

theorem orb_enum {l : Nat} (hl : l < 10) : classOrbits[l]! = orbRec l ∧
    treeOK (conjStep 42 dGens dInvs) dGens.size (classRep l) (orbRec l) = true := by
  rw [orbits_get hl]
  exact penumK_conj_sound base.1 fg_ok fgi_ok (rep_eq hl) (orb_hd hl)
    (fun _ hi => orb_pt hl hi)

theorem nget_getD' (L : List Nat) (i : Nat) : nget L i = L.getD i 0 := by
  induction L generalizing i with
  | nil => rfl
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

theorem orb_size {l : Nat} (hl : l < 10) : (orbRec l).tabs.size = classSizes.getD l 0 := by
  obtain ⟨-, hc⟩ := (bAnd_iff _ _).1 (allN_spec reps_ok l hl)
  simp only [orbRec, penumRec, Array.size_ofFn]
  rw [Nat.eq_of_beq_eq_true hc, nget_getD']

theorem orb_get {l q : Nat} (hl : l < 10) (hq : q < OF.C l) :
    (orbRec l).tabs[q]! = unpack 42 6 (offF OF.T (OF.TO l) q) ∧
      canonK 42 6 (mask 6) (42 * 6) (offF OF.T (OF.TO l) q) = true := by
  refine ⟨?_, penumPt_canon (orb_pt hl hq)⟩
  rw [getElem!_pos _ q (by simp [orbRec, penumRec, hq])]
  simp [orbRec, penumRec]

theorem root_canon {l : Nat} (hl : l < 10) : canonK 42 6 (mask 6) (42 * 6) (OF.R l) = true := by
  have hh := orb_hd hl
  unfold penumHdK at hh
  obtain ⟨h0, -, hr, -⟩ := (by simpa only [bAnd_iff] using hh :
    Nat.blt 0 (OF.C l) = true ∧ Nat.ble (OF.C l) 5000 = true ∧
      Nat.beq (offF OF.T (OF.TO l) 0) (OF.R l) = true ∧
      Nat.beq (CFSG.KS.PEnum.r32 (offF OF.PL (OF.PLO l)) 0) 0 = true)
  rw [← Nat.eq_of_beq_eq_true hr]
  exact (orb_get hl (Eq.mp Nat.blt_eq h0)).2

theorem rec_get {cnt i : Nat} {T PL : Nat → Nat} (hi : i < cnt) :
    (penumRec 42 6 cnt T PL).tabs[i]! = unpack 42 6 (T i) := by
  rw [getElem!_pos _ i (by simp [penumRec, hi])]
  simp [penumRec]

theorem facts0 : ((fixList 0).length = 42 ∧ (kGens 0).size = 22 ∧
      invsOK 42 (kGens 0) (kInvs 0) = true ∧ classOrbits.size = 10 ∧ classRep 0 = idTab 42)
    ∧ (enumOK 42 (kGens 0) (enumOf 42 (kGens 0) 40320) = true ∧
      (enumOf 42 (kGens 0) 40320).tabs.size = 40320)
    ∧ (enumOK 42 dGens (enumOf 42 dGens 20160) = true ∧
      (enumOf 42 dGens 20160).tabs.size = 20160 ∧
      normalOK 42 (enumOf 42 dGens 20160).tabs (kGens 0) (kInvs 0) dGens = true)
    ∧ ((∀ l < 10, orbitOK 42 dGens dInvs (classRep l) classOrbits[l]! = true ∧
        classOrbits[l]!.tabs.size = classSizes.getD l 0) ∧
      (∀ l < 10, ∀ l' < 10, l ≠ l' → notInOK classOrbits[l]!.tabs (classRep l') = true))
    ∧ (∀ k < (enumOf 42 dGens 20160).tabs.size, ∃ l < 10,
      found (indexOf classOrbits[l]!.tabs) classOrbits[l]!.tabs
        (enumOf 42 dGens 20160).tabs[k]! = true) := by
  refine ⟨⟨by rw [fix_eq0]; exact fix0_facts.1, kgens0_size, invsK0, by simp [classOrbits], rfl⟩,
    ⟨by rw [k_enum.1]; exact k_enum.2, by rw [k_enum.1]; simp [penumRec]; rfl⟩,
    ⟨by rw [d_enum.1]; exact d_enum.2, by rw [d_enum.1]; simp [penumRec]; rfl,
      by rw [d_enum.1]; exact normal⟩, ⟨fun l hl => ?_, fun l hl l' hl' hne => ?_⟩, ?_⟩
  · obtain ⟨e, ht⟩ := orb_enum hl
    rw [e]
    refine ⟨?_, orb_size hl⟩
    unfold orbitOK
    rw [invsD, ht]
    rfl
  · rw [(orb_enum hl).1, rep_eq hl']
    unfold notInOK allBelow
    rw [all_range_iff]
    intro q hq
    have hq' : q < OF.C l := by simpa [orbRec, penumRec] using hq
    obtain ⟨hg, hc⟩ := orb_get hl hq'
    rw [hg, beq_unpack hc (root_canon hl')]
    have hn := allN_spec (allN_spec notin l hl) l' hl'
    have hb : Nat.beq l l' = false := by
      cases h : Nat.beq l l'
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true h) hne
    rw [hb] at hn
    have hz := allN_spec hn q hq'
    cases h : Nat.beq (offF OF.T (OF.TO l) q) (OF.R l')
    · rfl
    · rw [h] at hz
      exact absurd hz (by decide)
  · rw [d_enum.1]
    intro k hk
    have hk' : k < DE.cnt := by simpa [penumRec] using hk
    have hc := cover_all (k := k) hk'
    unfold coverK at hc
    simp only [strictB_app'] at hc
    obtain ⟨hl, hq, he⟩ := (by simpa only [bAnd_iff] using hc :
      Nat.blt (Nat.shiftRight (COV k) 16) 10 = true ∧
      Nat.blt (Nat.land (COV k) 65535) (OF.C (Nat.shiftRight (COV k) 16)) = true ∧
      Nat.beq (offF OF.T (OF.TO (Nat.shiftRight (COV k) 16)) (Nat.land (COV k) 65535))
        (DE.T k) = true)
    have hl' := Eq.mp Nat.blt_eq hl
    refine ⟨Nat.shiftRight (COV k) 16, hl', ?_⟩
    rw [(orb_enum hl').1, rec_get hk']
    exact penum_found_sound (fun _ hx => orb_pt hl' hx) (Eq.mp Nat.blt_eq hq)
      (Nat.eq_of_beq_eq_true he)

end CertificateChecks.KernelSpor.SuzCT

end
