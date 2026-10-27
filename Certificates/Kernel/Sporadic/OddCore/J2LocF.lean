
module

public import Certificates.Kernel.Sporadic.OddCore.J2LocC2
public import Certificates.Kernel.Sporadic.OddCore.MulHGlue
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue3
meta import Certificates.Kernel.Sporadic.OddCore.J2Loc
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Sporadic.SmallOddCore.ClassSimple

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.J2Loc

open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier.Native CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum
open CFSG.KS.MulH CFSG.KC.BfsPin CFSG.Monster.B.Co2.Native

meta def repIM : Array (Array Nat) :=
  (List.range 4).toArray.map fun r => CFSG.Monster.B.Co2.Native.invCand 315 (repM r)

end CertificateChecks.KernelSpor.J2Loc

#kmisc_packarrs CertificateChecks.KernelSpor.J2RI CertificateChecks.KernelSpor.J2Loc.repIM 9

namespace CertificateChecks.KernelSpor.J2Loc

open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier.Native CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum
open CFSG.KS.MulH CFSG.KC.BfsPin CFSG.Monster.B.Co2.Native

theorem base_ok : bAnd(szOK 315 9, bAnd(canonK 315 9 (mask 9) (315 * 9) idK,
    bAnd(CFSG.KS.Prim.idK 315 9 (mask 9), bAnd(invEqK 315 9 (mask 9) (315 * 9) J2O0.R (J2RI 0),
    bAnd(invEqK 315 9 (mask 9) (315 * 9) J2O1.R (J2RI 1),
    bAnd(invEqK 315 9 (mask 9) (315 * 9) J2O2.R (J2RI 2),
    invEqK 315 9 (mask 9) (315 * 9) J2O3.R (J2RI 3))))))) = true := by
  quickRfl

theorem base : szOK 315 9 = true ∧ canonK 315 9 (mask 9) (315 * 9) idK = true ∧
    CFSG.KS.Prim.idK 315 9 (mask 9) = true ∧
    invEqK 315 9 (mask 9) (315 * 9) J2O0.R (J2RI 0) = true ∧
    invEqK 315 9 (mask 9) (315 * 9) J2O1.R (J2RI 1) = true ∧
    invEqK 315 9 (mask 9) (315 * 9) J2O2.R (J2RI 2) = true ∧
    invEqK 315 9 (mask 9) (315 * 9) J2O3.R (J2RI 3) = true := by
  simpa only [bAnd_iff] using base_ok

theorem hn : szOK 315 9 = true := base.1

theorem hidc : canonK 315 9 (mask 9) (315 * 9) (pidn 315 9) = true := base.2.1

theorem hid : idT 315 = tabT (unpack 315 9 (pidn 315 9)) := by
  rw [idT_tabT, idK_sound base.2.2.1]

theorem reps_inv : invEqK 315 9 (mask 9) (315 * 9) J2O0.R (J2RI 0) = true ∧
    invEqK 315 9 (mask 9) (315 * 9) J2O1.R (J2RI 1) = true ∧
    invEqK 315 9 (mask 9) (315 * 9) J2O2.R (J2RI 2) = true ∧
    invEqK 315 9 (mask 9) (315 * 9) J2O3.R (J2RI 3) = true := base.2.2.2

theorem gens : (allN 5 (fun j => canonK 315 9 (mask 9) (315 * 9) (c1L (Nat.succ j))) = true ∧
    allN 4 (fun j => canonK 315 9 (mask 9) (315 * 9) (c2L (Nat.succ j))) = true ∧
    allN 5 (fun j => Nat.beq (J2C1.GI j) (c1L (Nat.succ j))) = true ∧
    allN 4 (fun j => Nat.beq (J2C2.GI j) (c2L (Nat.succ j))) = true ∧
    allN 5 (fun j => invEqK 315 9 (mask 9) (315 * 9) (J2C1.GI j) (J2C1I j)) = true ∧
    allN 4 (fun j => invEqK 315 9 (mask 9) (315 * 9) (J2C2.GI j) (J2C2I j)) = true) ∧
    (Nat.beq (J2D.GI 0) (wfoldK 315 9 (mask 9) c1L [3, 2] idK) = true ∧
    Nat.beq (J2D.GI 1) (wfoldK 315 9 (mask 9) c1L [2, 4, 2, 4] idK) = true ∧
    allN 2 (fun j => invEqK 315 9 (mask 9) (315 * 9) (J2D.GI j) (J2DI j)) = true) ∧
    (Nat.beq (J2Q.GI 0) (wfoldK 315 9 (mask 9) c2L [3, 3, 3, 2, 1, 2, 1] idK) = true ∧
    Nat.beq (J2Q.GI 1) (wfoldK 315 9 (mask 9) c2L [3, 3, 2, 3, 2, 1] idK) = true ∧
    Nat.beq (J2Q.GI 2) (wfoldK 315 9 (mask 9) c2L [2, 3, 1, 3, 3, 1] idK) = true ∧
    Nat.beq (J2Q.GI 3) (wfoldK 315 9 (mask 9) c2L [3, 3, 3] idK) = true ∧
    Nat.beq (J2Q.GI 4) (wfoldK 315 9 (mask 9) c2L [4, 4, 4] idK) = true ∧
    allN 5 (fun j => invEqK 315 9 (mask 9) (315 * 9) (J2Q.GI j) (J2QI j)) = true) := by
  have h := gens_ok
  simp only [bAnd_iff] at h
  obtain ⟨a1, a2, a3, a4, a5, a6, b1, b2, b3, c1, c2, c3, c4, c5, c6⟩ := h
  exact ⟨⟨a1, a2, a3, a4, a5, a6⟩, ⟨b1, b2, b3⟩, ⟨c1, c2, c3, c4, c5, c6⟩⟩

theorem cent_tab {k : Nat} (hk : k < 42) : j2CentTbl k = tabT (unpack 315 9 (J2CentT.F k)) := by
  rw [← OddCore.j2CentTbl_eq hk, tabT_natArr]

theorem c1L_ok {l : Nat} (h1 : 1 ≤ l) (h5 : l ≤ 5) :
    j2C1Gens.getD (l - 1) (idT 315) = tabT (unpack 315 9 (c1L l)) ∧
      canonK 315 9 (mask 9) (315 * 9) (c1L l) = true := by
  have hc := allN_spec gens.1.1 (l - 1) (by omega)
  have e : Nat.succ (l - 1) = l := by omega
  rw [e] at hc
  refine ⟨?_, hc⟩
  interval_cases l <;> simp only [j2C1Gens, Nat.reduceSub, List.getD_cons_succ, List.getD_cons_zero]
  · exact cent_tab (k := 18) (by norm_num)
  · exact cent_tab (k := 19) (by norm_num)
  · exact cent_tab (k := 20) (by norm_num)
  · exact cent_tab (k := 21) (by norm_num)
  · exact cent_tab (k := 22) (by norm_num)

theorem c2L_ok {l : Nat} (h1 : 1 ≤ l) (h4 : l ≤ 4) :
    j2C2Gens.getD (l - 1) (idT 315) = tabT (unpack 315 9 (c2L l)) ∧
      canonK 315 9 (mask 9) (315 * 9) (c2L l) = true := by
  have hc := allN_spec gens.1.2.1 (l - 1) (by omega)
  have e : Nat.succ (l - 1) = l := by omega
  rw [e] at hc
  refine ⟨?_, hc⟩
  interval_cases l <;> simp only [j2C2Gens, Nat.reduceSub, List.getD_cons_succ, List.getD_cons_zero]
  · exact cent_tab (k := 32) (by norm_num)
  · exact cent_tab (k := 33) (by norm_num)
  · exact cent_tab (k := 34) (by norm_num)
  · exact cent_tab (k := 35) (by norm_num)

theorem c1_tabs : TabsOK 315 9 5 J2C1.GI j2C1Gens.toArray := by
  refine ⟨rfl, fun j hj => ?_⟩
  have e := Nat.eq_of_beq_eq_true (allN_spec gens.1.2.2.1 j hj)
  obtain ⟨h1, h2⟩ := c1L_ok (l := Nat.succ j) (by omega) (by omega)
  rw [e, ← h1]
  refine ⟨?_, h2⟩
  rw [List.getElem!_toArray]
  interval_cases j <;> rfl

theorem c2_tabs : TabsOK 315 9 4 J2C2.GI j2C2Gens.toArray := by
  refine ⟨rfl, fun j hj => ?_⟩
  have e := Nat.eq_of_beq_eq_true (allN_spec gens.1.2.2.2.1 j hj)
  obtain ⟨h1, h2⟩ := c2L_ok (l := Nat.succ j) (by omega) (by omega)
  rw [e, ← h1]
  refine ⟨?_, h2⟩
  rw [List.getElem!_toArray]
  interval_cases j <;> rfl

theorem word1 {wd : List Nat} (hw : ∀ l ∈ wd, 1 ≤ l ∧ l ≤ 5) :
    wordTbl 315 j2C1Gens wd = tabT (unpack 315 9 (wfoldK 315 9 (mask 9) c1L wd (pidn 315 9))) ∧
      canonK 315 9 (mask 9) (315 * 9) (wfoldK 315 9 (mask 9) c1L wd (pidn 315 9)) = true :=
  wordTbl_unpack hid hidc fun l hl => c1L_ok (hw l hl).1 (hw l hl).2

theorem word2 {wd : List Nat} (hw : ∀ l ∈ wd, 1 ≤ l ∧ l ≤ 4) :
    wordTbl 315 j2C2Gens wd = tabT (unpack 315 9 (wfoldK 315 9 (mask 9) c2L wd (pidn 315 9))) ∧
      canonK 315 9 (mask 9) (315 * 9) (wfoldK 315 9 (mask 9) c2L wd (pidn 315 9)) = true :=
  wordTbl_unpack hid hidc fun l hl => c2L_ok (hw l hl).1 (hw l hl).2

theorem d_tabs : TabsOK 315 9 2 J2D.GI j2DGens.toArray := by
  refine ⟨rfl, fun j hj => ?_⟩
  interval_cases j
  · obtain ⟨h1, h2⟩ := word1 (wd := [3, 2]) (by decide)
    rw [Nat.eq_of_beq_eq_true gens.2.1.1]
    exact ⟨h1, h2⟩
  · obtain ⟨h1, h2⟩ := word1 (wd := [2, 4, 2, 4]) (by decide)
    rw [Nat.eq_of_beq_eq_true gens.2.1.2.1]
    exact ⟨h1, h2⟩

theorem q_tabs : TabsOK 315 9 5 J2Q.GI j2QGens.toArray := by
  refine ⟨rfl, fun j hj => ?_⟩
  obtain ⟨q0, q1, q2, q3, q4, -⟩ := gens.2.2
  interval_cases j
  · obtain ⟨h1, h2⟩ := word2 (wd := [3, 3, 3, 2, 1, 2, 1]) (by decide)
    rw [Nat.eq_of_beq_eq_true q0]
    exact ⟨h1, h2⟩
  · obtain ⟨h1, h2⟩ := word2 (wd := [3, 3, 2, 3, 2, 1]) (by decide)
    rw [Nat.eq_of_beq_eq_true q1]
    exact ⟨h1, h2⟩
  · obtain ⟨h1, h2⟩ := word2 (wd := [2, 3, 1, 3, 3, 1]) (by decide)
    rw [Nat.eq_of_beq_eq_true q2]
    exact ⟨h1, h2⟩
  · obtain ⟨h1, h2⟩ := word2 (wd := [3, 3, 3]) (by decide)
    rw [Nat.eq_of_beq_eq_true q3]
    exact ⟨h1, h2⟩
  · obtain ⟨h1, h2⟩ := word2 (wd := [4, 4, 4]) (by decide)
    rw [Nat.eq_of_beq_eq_true q4]
    exact ⟨h1, h2⟩

theorem invs_ok : bAnd(allN 5 (fun j => canonK 315 9 (mask 9) (315 * 9) (J2C1I j)),
    bAnd(allN 4 (fun j => canonK 315 9 (mask 9) (315 * 9) (J2C2I j)),
    bAnd(allN 2 (fun j => canonK 315 9 (mask 9) (315 * 9) (J2DI j)),
    bAnd(allN 5 (fun j => canonK 315 9 (mask 9) (315 * 9) (J2QI j)),
    allN 4 (fun j => canonK 315 9 (mask 9) (315 * 9) (J2RI j)))))) = true := by
  quickRfl

theorem inv_of {k : Nat} {G GI : Nat → Nat}
    (h : allN k (fun j => invEqK 315 9 (mask 9) (315 * 9) (G j) (GI j)) = true)
    (hc : allN k (fun j => canonK 315 9 (mask 9) (315 * 9) (GI j)) = true) :
    ∀ j < k, invEqK 315 9 (mask 9) (315 * 9) (G j) (GI j) = true ∧
      canonK 315 9 (mask 9) (315 * 9) (GI j) = true :=
  fun j hj => ⟨allN_spec h j hj, allN_spec hc j hj⟩

theorem invs : (allN 5 (fun j => canonK 315 9 (mask 9) (315 * 9) (J2C1I j)) = true ∧
    allN 4 (fun j => canonK 315 9 (mask 9) (315 * 9) (J2C2I j)) = true ∧
    allN 2 (fun j => canonK 315 9 (mask 9) (315 * 9) (J2DI j)) = true ∧
    allN 5 (fun j => canonK 315 9 (mask 9) (315 * 9) (J2QI j)) = true ∧
    allN 4 (fun j => canonK 315 9 (mask 9) (315 * 9) (J2RI j)) = true) := by
  simpa only [bAnd_iff] using invs_ok

theorem sl_all {cnt : Nat} {P : Nat → Bool} (h : slK cnt P 0 cnt = true) : ∀ c < cnt, P c = true :=
  fun c hc => slK_spec h c (Nat.zero_le _) (by omega) hc

theorem pe_all {k cnt : Nat} {G GI T PL POS SRT SRI : Nat → Nat}
    (h : penumSlK 315 9 (mask 9) (315 * 9) true G GI k cnt T PL POS SRT SRI 0 cnt = true) :
    ∀ i < cnt, penumPtK 315 9 (mask 9) (315 * 9) true G GI k cnt T PL POS SRT SRI i = true :=
  fun i hi => penumSl_spec h i (Nat.zero_le _) (by omega) hi

theorem cover {L N : Nat} {P : Nat → Prop} (hL : 0 < L)
    (h : ∀ s < N, ∀ i, L * s ≤ i → i < L * s + L → P i) : ∀ i < L * N, P i := by
  intro i hi
  refine h (i / L) (Nat.div_lt_of_lt_mul hi) i (Nat.mul_div_le i L) ?_
  have := Nat.lt_mul_div_succ i hL
  rw [Nat.mul_add, Nat.mul_one] at this
  exact this

theorem hd : (penumHdK idK J2D.cnt 100 J2D.T J2D.PL = true ∧
    penumHdK idK J2C1.cnt 300 J2C1.T J2C1.PL = true ∧ penumHdK idK J2Q.cnt 100 J2Q.T J2Q.PL = true ∧
    penumHdK idK J2C2.cnt 3000 J2C2.T J2C2.PL = true) ∧
    (penumHdK J2O0.R J2O0.cnt 100 J2O0.T J2O0.PL = true ∧
    penumHdK J2O1.R J2O1.cnt 100 J2O1.T J2O1.PL = true ∧
    penumHdK J2O2.R J2O2.cnt 100 J2O2.T J2O2.PL = true ∧
    penumHdK J2O3.R J2O3.cnt 100 J2O3.T J2O3.PL = true) ∧
    (penumHdK idK J2N0.cnt 100 J2N0.T J2N0.PL = true ∧
    penumHdK idK J2N1.cnt 100 J2N1.T J2N1.PL = true ∧
    penumHdK idK J2N2.cnt 100 J2N2.T J2N2.PL = true ∧
    penumHdK idK J2N3.cnt 100 J2N3.T J2N3.PL = true) := by
  have h := heads
  simp only [bAnd_iff] at h
  obtain ⟨a1, a2, a3, a4, b1, b2, b3, b4, c1, c2, c3, c4⟩ := h
  exact ⟨⟨a1, a2, a3, a4⟩, ⟨b1, b2, b3, b4⟩, ⟨c1, c2, c3, c4⟩⟩

theorem idv : (allN 2 (fun j => Nat.beq (J2D.G j) idK) = true ∧
    allN 5 (fun j => Nat.beq (J2C1.G j) idK) = true ∧
    allN 5 (fun j => Nat.beq (J2Q.G j) idK) = true ∧
    allN 4 (fun j => Nat.beq (J2C2.G j) idK) = true) ∧
    (allN J2O0.cnt (fun j => Nat.beq (J2N0.G j) idK) = true ∧
    allN J2O1.cnt (fun j => Nat.beq (J2N1.G j) idK) = true ∧
    allN J2O2.cnt (fun j => Nat.beq (J2N2.G j) idK) = true ∧
    allN J2O3.cnt (fun j => Nat.beq (J2N3.G j) idK) = true) := by
  have h := ids_ok
  simp only [bAnd_iff] at h
  obtain ⟨a1, a2, a3, a4, b1, b2, b3, b4⟩ := h
  exact ⟨⟨a1, a2, a3, a4⟩, ⟨b1, b2, b3, b4⟩⟩

theorem ids_of {k : Nat} {G : Nat → Nat} (h : allN k (fun j => Nat.beq (G j) idK) = true) :
    ∀ j < k, G j = pidn 315 9 := fun j hj => Nat.eq_of_beq_eq_true (allN_spec h j hj)

theorem c2_pe : ∀ i < J2C2.cnt, penumPtK 315 9 (mask 9) (315 * 9) true J2C2.G J2C2.GI 4 J2C2.cnt
    J2C2.T J2C2.PL J2C2.POS J2C2.SRT J2C2.SRI i = true := by
  have hc : J2C2.cnt = 240 * 8 := rfl
  rw [hc]
  refine cover (by norm_num) fun s hs i h1 h2 => ?_
  have hi : i < J2C2.cnt := by rw [hc]; omega
  interval_cases s
  · exact penumSl_spec c2E0 i h1 h2 hi
  · exact penumSl_spec c2E1 i h1 h2 hi
  · exact penumSl_spec c2E2 i h1 h2 hi
  · exact penumSl_spec c2E3 i h1 h2 hi
  · exact penumSl_spec c2E4 i h1 h2 hi
  · exact penumSl_spec c2E5 i h1 h2 hi
  · exact penumSl_spec c2E6 i h1 h2 hi
  · exact penumSl_spec c2E7 i h1 h2 hi

theorem c2_hs :
    ∀ i < J2C2.cnt, hsortPtK 315 9 (mask 9) J2C2.cnt J2C2.T J2C2.HS J2C2.HSI i = true := by
  have hc : J2C2.cnt = 480 * 4 := rfl
  rw [hc]
  refine cover (by norm_num) fun s hs i h1 h2 => ?_
  have hi : i < J2C2.cnt := by rw [hc]; omega
  interval_cases s
  · exact slK_spec c2H0 i h1 h2 hi
  · exact slK_spec c2H1 i h1 h2 hi
  · exact slK_spec c2H2 i h1 h2 hi
  · exact slK_spec c2H3 i h1 h2 hi

theorem c2_cl : ∀ c < J2C2.cnt * (4 + 4), findPtK J2C2.cnt J2C2.T
    (prodQK 315 9 (mask 9) (4 + 4) J2C2.T (bothK 4 J2C2.GI J2C2I)) J2C2Cl c = true := by
  have hc : J2C2.cnt * (4 + 4) = 1920 * 8 := rfl
  rw [hc]
  refine cover (by norm_num) fun s hs i h1 h2 => ?_
  have hi : i < Nat.mul J2C2.cnt 8 := by
    change i < J2C2.cnt * 8
    have : J2C2.cnt * 8 = 1920 * 8 := rfl
    omega
  interval_cases s
  · exact slK_spec c2Cl0 i h1 h2 hi
  · exact slK_spec c2Cl1 i h1 h2 hi
  · exact slK_spec c2Cl2 i h1 h2 hi
  · exact slK_spec c2Cl3 i h1 h2 hi
  · exact slK_spec c2Cl4 i h1 h2 hi
  · exact slK_spec c2Cl5 i h1 h2 hi
  · exact slK_spec c2Cl6 i h1 h2 hi
  · exact slK_spec c2Cl7 i h1 h2 hi

theorem d_rec : mulClosureH 315 j2DGens.toArray 100 = hRec 315 9 J2D.cnt J2D.T J2D.PL :=
  (mulH_sound hn (ids_of idv.1.1) d_tabs hd.1.1 (pe_all dE) (sl_all dH)).1

theorem d_enum : enumOK 315 100 60 j2DGens = true :=
  enumOK_of hn (ids_of idv.1.1) d_tabs (inv_of gens.2.1.2.2 invs.2.2.1) hd.1.1 (pe_all dE)
    (sl_all dH) (sl_all dCl) rfl

theorem c1_enum : enumOK 315 300 240 j2C1Gens = true :=
  enumOK_of hn (ids_of idv.1.2.1) c1_tabs (inv_of gens.1.2.2.2.2.1 invs.1) hd.1.2.1 (pe_all c1E)
    (sl_all c1H) (sl_all c1Cl) rfl

theorem q_enum : enumOK 315 100 32 j2QGens = true :=
  enumOK_of hn (ids_of idv.1.2.2.1) q_tabs (inv_of gens.2.2.2.2.2.2.2 invs.2.2.2.1) hd.1.2.2.1
    (pe_all qE) (sl_all qH) (sl_all qCl) rfl

theorem c2_enum : enumOK 315 3000 1920 j2C2Gens = true :=
  enumOK_of hn (ids_of idv.1.2.2.2) c2_tabs (inv_of gens.1.2.2.2.2.2 invs.2.1) hd.1.2.2.2 c2_pe
    c2_hs c2_cl rfl

theorem d_norm : normOK 315 100 j2DGens j2C1Gens = true :=
  normOK_of hn (ids_of idv.1.1) d_tabs hd.1.1 (pe_all dE) (sl_all dH) c1_tabs
    (inv_of gens.1.2.2.2.2.1 invs.1) (sl_all dNm)

theorem q_norm : normOK 315 100 j2QGens j2C2Gens = true :=
  normOK_of hn (ids_of idv.1.2.2.1) q_tabs hd.1.2.2.1 (pe_all qE) (sl_all qH) c2_tabs
    (inv_of gens.1.2.2.2.2.2 invs.2.1) (sl_all qNm)

theorem perms_of {k : Nat} {G GI : Nat → Nat} {gs : List Table} (hg : TabsOK 315 9 k G gs.toArray)
    (hi : ∀ j < k, invEqK 315 9 (mask 9) (315 * 9) (G j) (GI j) = true ∧
      canonK 315 9 (mask 9) (315 * 9) (GI j) = true) :
    gs.all (fun c => permOK 315 c) = true := by
  rw [List.all_eq_true]
  intro g hgm
  obtain ⟨j, hj, rfl, hc⟩ := TabsOK_list hg hgm
  exact permOK_unpack hc (hi j hj).1

theorem dL_ok {l : Nat} (h1 : 1 ≤ l) (h2 : l ≤ 2) :
    j2DGens.getD (l - 1) (idT 315) = tabT (unpack 315 9 (dL l)) ∧
      canonK 315 9 (mask 9) (315 * 9) (dL l) = true := by
  have h := d_tabs.2 (l - 1) (by omega)
  interval_cases l
  · exact h
  · exact h

theorem wordD {wd : List Nat} (hw : ∀ l ∈ wd, 1 ≤ l ∧ l ≤ 2) :
    wordTbl 315 j2DGens wd = tabT (unpack 315 9 (wfoldK 315 9 (mask 9) dL wd (pidn 315 9))) ∧
      canonK 315 9 (mask 9) (315 * 9) (wfoldK 315 9 (mask 9) dL wd (pidn 315 9)) = true :=
  wordTbl_unpack hid hidc fun l hl => dL_ok (hw l hl).1 (hw l hl).2

theorem repv : (Nat.beq J2O0.R (wfoldK 315 9 (mask 9) dL [1] idK) = true ∧
    Nat.beq J2O1.R (wfoldK 315 9 (mask 9) dL [2] idK) = true ∧
    Nat.beq J2O2.R (wfoldK 315 9 (mask 9) dL [1, 2] idK) = true ∧
    Nat.beq J2O3.R (wfoldK 315 9 (mask 9) dL [1, 2, 2] idK) = true) ∧
    (allN 2 (fun j => bAnd(Nat.beq (J2O0.G j) (J2D.GI j), Nat.beq (J2O0.GI j) (J2DI j))) = true ∧
    allN 2 (fun j => bAnd(Nat.beq (J2O1.G j) (J2D.GI j), Nat.beq (J2O1.GI j) (J2DI j))) = true ∧
    allN 2 (fun j => bAnd(Nat.beq (J2O2.G j) (J2D.GI j), Nat.beq (J2O2.GI j) (J2DI j))) = true ∧
    allN 2 (fun j => bAnd(Nat.beq (J2O3.G j) (J2D.GI j), Nat.beq (J2O3.GI j) (J2DI j))) = true) ∧
    (allN J2O0.cnt (fun j => Nat.beq (J2N0.GI j) (J2O0.T j)) = true ∧
    allN J2O1.cnt (fun j => Nat.beq (J2N1.GI j) (J2O1.T j)) = true ∧
    allN J2O2.cnt (fun j => Nat.beq (J2N2.GI j) (J2O2.T j)) = true ∧
    allN J2O3.cnt (fun j => Nat.beq (J2N3.GI j) (J2O3.T j)) = true) := by
  have h := reps_ok
  simp only [bAnd_iff] at h
  obtain ⟨a1, a2, a3, a4, b1, b2, b3, b4, c1, c2, c3, c4⟩ := h
  exact ⟨⟨a1, a2, a3, a4⟩, ⟨b1, b2, b3, b4⟩, ⟨c1, c2, c3, c4⟩⟩

theorem pair_of {G GI : Nat → Nat}
    (h : allN 2 (fun j => bAnd(Nat.beq (G j) (J2D.GI j), Nat.beq (GI j) (J2DI j))) = true) :
    (∀ j < 2, G j = J2D.GI j) ∧ ∀ j < 2, GI j = J2DI j := by
  refine ⟨fun j hj => ?_, fun j hj => ?_⟩
  · exact Nat.eq_of_beq_eq_true ((bAnd_iff _ _).1 (allN_spec h j hj)).1
  · exact Nat.eq_of_beq_eq_true ((bAnd_iff _ _).1 (allN_spec h j hj)).2

theorem d_invs : ∀ j < 2, invEqK 315 9 (mask 9) (315 * 9) (J2D.GI j) (J2DI j) = true ∧
    canonK 315 9 (mask 9) (315 * 9) (J2DI j) = true := inv_of gens.2.1.2.2 invs.2.2.1

theorem o_rec_of {X cnt : Nat} {G GI T PL POS SRT SRI HS HSI : Nat → Nat} {r : Table}
    (hpair : allN 2 (fun j => bAnd(Nat.beq (G j) (J2D.GI j), Nat.beq (GI j) (J2DI j))) = true)
    (hr : r = tabT (unpack 315 9 X)) (hh : penumHdK X cnt 100 T PL = true)
    (hp : penumSlK 315 9 (mask 9) (315 * 9) true G GI 2 cnt T PL POS SRT SRI 0 cnt = true)
    (hs : slK cnt (hsortPtK 315 9 (mask 9) cnt T HS HSI) 0 cnt = true) :
    conjClosureH 315 j2DGens.toArray (j2DGens.toArray.map (invT 315)) r 100 = hRec 315 9 cnt T PL ∧
      conjTreeOK 315 j2DGens.toArray (j2DGens.toArray.map (invT 315)) r (hRec 315 9 cnt T PL).1
        (hRec 315 9 cnt T PL).2.1 (hRec 315 9 cnt T PL).2.2 = true ∧
      hkeysDistinct 315 (hRec 315 9 cnt T PL).1.toList = true := by
  obtain ⟨h1, h2⟩ := pair_of hpair
  exact conjH_sound hn (TabsOK_congr h1 d_tabs) (TabsOK_congr h2 (TabsOK_inv d_tabs d_invs)) hr hh
    (pe_all hp) (sl_all hs)

theorem rep_eq {X : Nat} {wd : List Nat} (hw : ∀ l ∈ wd, 1 ≤ l ∧ l ≤ 2)
    (h : Nat.beq X (wfoldK 315 9 (mask 9) dL wd idK) = true) :
    wordTbl 315 j2DGens wd = tabT (unpack 315 9 X) ∧ canonK 315 9 (mask 9) (315 * 9) X = true := by
  rw [Nat.eq_of_beq_eq_true h]
  exact wordD hw

theorem r0 : wordTbl 315 j2DGens [1] = tabT (unpack 315 9 J2O0.R) ∧
    canonK 315 9 (mask 9) (315 * 9) J2O0.R = true := rep_eq (by decide) repv.1.1

theorem r1 : wordTbl 315 j2DGens [2] = tabT (unpack 315 9 J2O1.R) ∧
    canonK 315 9 (mask 9) (315 * 9) J2O1.R = true := rep_eq (by decide) repv.1.2.1

theorem r2 : wordTbl 315 j2DGens [1, 2] = tabT (unpack 315 9 J2O2.R) ∧
    canonK 315 9 (mask 9) (315 * 9) J2O2.R = true := rep_eq (by decide) repv.1.2.2.1

theorem r3 : wordTbl 315 j2DGens [1, 2, 2] = tabT (unpack 315 9 J2O3.R) ∧
    canonK 315 9 (mask 9) (315 * 9) J2O3.R = true := rep_eq (by decide) repv.1.2.2.2

theorem bIf_or {a b : Bool} (h : bIf(a, true, b) = true) : a = true ∨ b = true := by
  cases a
  · exact Or.inr h
  · exact Or.inl rfl

theorem n_tabs_of {cntO : Nat} {TO PLO GN : Nat → Nat}
    (he : allN cntO (fun j => Nat.beq (GN j) (TO j)) = true)
    (hc : ∀ j < cntO, canonK 315 9 (mask 9) (315 * 9) (TO j) = true) :
    TabsOK 315 9 cntO GN (hRec 315 9 cntO TO PLO).1 := by
  refine ⟨hRec_size _ _ _ _ _, fun j hj => ?_⟩
  rw [hRec_get hj, Nat.eq_of_beq_eq_true (allN_spec he j hj)]
  exact ⟨rfl, hc j hj⟩

theorem canon_of {k cnt : Nat} {G GI T PL POS SRT SRI : Nat → Nat}
    (h : penumSlK 315 9 (mask 9) (315 * 9) true G GI k cnt T PL POS SRT SRI 0 cnt = true) :
    ∀ i < cnt, canonK 315 9 (mask 9) (315 * 9) (T i) = true :=
  fun i hi => penumPt_canon (pe_all h i hi)

theorem class_ok {cntO cntN : Nat} {GO GIO TO PLO POSO SRTO SRIO HSO HSIO : Nat → Nat}
    {GN GIN TN PLN POSN SRTN SRIN HSN HSIN : Nat → Nat} {r : Table} {X : Nat}
    (hpair : allN 2 (fun j => bAnd(Nat.beq (GO j) (J2D.GI j), Nat.beq (GIO j) (J2DI j))) = true)
    (hr : r = tabT (unpack 315 9 X)) (hh : penumHdK X cntO 100 TO PLO = true)
    (hp : penumSlK 315 9 (mask 9) (315 * 9) true GO GIO 2 cntO TO PLO POSO SRTO SRIO 0 cntO = true)
    (hs : slK cntO (hsortPtK 315 9 (mask 9) cntO TO HSO HSIO) 0 cntO = true)
    (hNG : allN cntO (fun j => Nat.beq (GN j) idK) = true)
    (hNe : allN cntO (fun j => Nat.beq (GIN j) (TO j)) = true)
    (hNh : penumHdK idK cntN 100 TN PLN = true)
    (hNp : penumSlK 315 9 (mask 9) (315 * 9) true GN GIN cntO cntN TN PLN POSN SRTN SRIN 0 cntN =
      true)
    (hNs : slK cntN (hsortPtK 315 9 (mask 9) cntN TN HSN HSIN) 0 cntN = true) (hN : cntN = 60) :
    (conjTreeOK 315 j2DGens.toArray (j2DGens.toArray.map (invT 315)) r
      (conjClosureH 315 j2DGens.toArray (j2DGens.toArray.map (invT 315)) r 100).1
      (conjClosureH 315 j2DGens.toArray (j2DGens.toArray.map (invT 315)) r 100).2.1
      (conjClosureH 315 j2DGens.toArray (j2DGens.toArray.map (invT 315)) r 100).2.2 &&
    (mulTreeOK 315 (conjClosureH 315 j2DGens.toArray (j2DGens.toArray.map (invT 315)) r 100).1
      (mulClosureH 315 (conjClosureH 315 j2DGens.toArray (j2DGens.toArray.map (invT 315)) r
        100).1 100).1
      (mulClosureH 315 (conjClosureH 315 j2DGens.toArray (j2DGens.toArray.map (invT 315)) r
        100).1 100).2.1
      (mulClosureH 315 (conjClosureH 315 j2DGens.toArray (j2DGens.toArray.map (invT 315)) r
        100).1 100).2.2 &&
      hkeysDistinct 315 (mulClosureH 315 (conjClosureH 315 j2DGens.toArray
        (j2DGens.toArray.map (invT 315)) r 100).1 100).1.toList &&
      (mulClosureH 315 (conjClosureH 315 j2DGens.toArray (j2DGens.toArray.map (invT 315)) r
        100).1 100).1.size == 60)) = true := by
  obtain ⟨e, t, -⟩ := o_rec_of hpair hr hh hp hs
  obtain ⟨e2, t2, d2⟩ := mulH_sound hn (ids_of hNG) (n_tabs_of (PLO := PLO) hNe (canon_of hp)) hNh
    (pe_all hNp) (sl_all hNs)
  rw [e, e2]
  simp only [Bool.and_eq_true, beq_iff_eq]
  exact ⟨t, ⟨t2, d2⟩, by rw [hRec_size, hN]⟩

theorem w0 : wordTbl 315 j2C1Gens [3, 2] = tabT (unpack 315 9 (J2D.GI 0)) := by
  rw [Nat.eq_of_beq_eq_true gens.2.1.1]
  exact (word1 (by decide)).1

theorem w1 : wordTbl 315 j2C1Gens [2, 4, 2, 4] = tabT (unpack 315 9 (J2D.GI 1)) := by
  rw [Nat.eq_of_beq_eq_true gens.2.1.2.1]
  exact (word1 (by decide)).1

theorem dg_canon : canonK 315 9 (mask 9) (315 * 9) (J2D.GI 0) = true ∧
    canonK 315 9 (mask 9) (315 * 9) (J2D.GI 1) = true :=
  ⟨(d_tabs.2 0 (by decide)).2, (d_tabs.2 1 (by decide)).2⟩

theorem all_comm_eq {k : Nat} {G : Nat → Nat} {gs : List Table} (hg : TabsOK 315 9 k G gs.toArray)
    {X : Nat} (hX : canonK 315 9 (mask 9) (315 * 9) X = true) :
    (gs.all fun g => commTT 315 (tabT (unpack 315 9 X)) g) =
      allN k (fun j => Nat.beq (pc X (G j)) (pc (G j) X)) := by
  rw [Bool.eq_iff_iff, List.all_eq_true, allN_iff]
  constructor
  · intro h j hj
    have hj' : j < gs.length := by have := hg.1; simp at this; omega
    have hm : gs[j] ∈ gs := List.getElem_mem hj'
    have hget : gs[j] = tabT (unpack 315 9 (G j)) := by
      rw [← (hg.2 j hj).1, getElem!_pos _ j (by simpa using hj')]
      simp
    have := h _ hm
    rw [hget, commTT_unpack hX (hg.2 j hj).2] at this
    exact this
  · intro h g hgm
    obtain ⟨j, hj, rfl, hc⟩ := TabsOK_list hg hgm
    rw [commTT_unpack hX hc]
    exact h j hj

theorem allN_two (f : Nat → Bool) : allN 2 f = bAnd(f 0, f 1) := by
  rw [Bool.eq_iff_iff, allN_iff, bAnd_iff]
  constructor
  · intro h
    exact ⟨h 0 (by decide), h 1 (by decide)⟩
  · rintro ⟨h0, h1⟩ j hj
    interval_cases j
    · exact h0
    · exact h1

theorem cent_d : centCount 315 300 j2C1Gens j2DGens = 4 := by
  rw [centCount_eq (q := fun i => strictB (J2C1.T i) (fun y =>
      bAnd(Nat.beq (pc y (J2D.GI 0)) (pc (J2D.GI 0) y),
        Nat.beq (pc y (J2D.GI 1)) (pc (J2D.GI 1) y))))
    (hi := 4) hn (ids_of idv.1.2.1) c1_tabs hd.1.2.1 (pe_all c1E) (sl_all c1H)
    (by decide) (fun i hi => by
      rw [all_comm_eq d_tabs (canon_of c1E i hi), allN_two, strictB_eq''])]
  exact Nat.eq_of_beq_eq_true cent1

theorem qC_all : ∀ i < J2C2.cnt, qOK i = true := by
  have hc : J2C2.cnt = 320 * 6 := rfl
  rw [hc]
  refine cover (by norm_num) fun s hs i h1 h2 => ?_
  have hi : i < J2C2.cnt := by rw [hc]; omega
  interval_cases s
  · exact slK_spec qC0 i h1 h2 hi
  · exact slK_spec qC1 i h1 h2 hi
  · exact slK_spec qC2 i h1 h2 hi
  · exact slK_spec qC3 i h1 h2 hi
  · exact slK_spec qC4 i h1 h2 hi
  · exact slK_spec qC5 i h1 h2 hi

theorem qOK_eq {i : Nat} (h : qOK i = true) : qComm i = lmemK CQ i := by
  unfold qOK at h
  cases h1 : qComm i <;> cases h2 : lmemK CQ i <;> simp_all

theorem cent_q : centCount 315 3000 j2C2Gens j2QGens = 2 := by
  rw [centCount_eq (q := qComm) (hi := 30) hn (ids_of idv.1.2.2.2) c2_tabs hd.1.2.2.2 c2_pe c2_hs
    (by decide) (fun i hi => by
      rw [all_comm_eq q_tabs (penumPt_canon (c2_pe i hi))]
      unfold qComm
      rw [strictB_eq''])]
  have e : cntBelowK J2C2.cnt qComm 30 = cntBelowK J2C2.cnt (lmemK CQ) 30 := by
    unfold cntBelowK
    rw [cntK_eq, cntK_eq, countP_range_lt _ (by decide), countP_range_lt _ (by decide)]
    apply List.countP_congr
    intro i hi
    rw [qOK_eq (qC_all i (List.mem_range.1 hi))]
  rw [e]
  exact Nat.eq_of_beq_eq_true cq_cnt

theorem o_recs :
    (conjClosureH 315 j2DGens.toArray (j2DGens.toArray.map (invT 315)) (wordTbl 315 j2DGens [1])
      100 = hRec 315 9 J2O0.cnt J2O0.T J2O0.PL) ∧
    (conjClosureH 315 j2DGens.toArray (j2DGens.toArray.map (invT 315)) (wordTbl 315 j2DGens [2])
      100 = hRec 315 9 J2O1.cnt J2O1.T J2O1.PL) ∧
    (conjClosureH 315 j2DGens.toArray (j2DGens.toArray.map (invT 315))
      (wordTbl 315 j2DGens [1, 2]) 100 = hRec 315 9 J2O2.cnt J2O2.T J2O2.PL) ∧
    (conjClosureH 315 j2DGens.toArray (j2DGens.toArray.map (invT 315))
      (wordTbl 315 j2DGens [1, 2, 2]) 100 = hRec 315 9 J2O3.cnt J2O3.T J2O3.PL) :=
  ⟨(o_rec_of repv.2.1.1 r0.1 hd.2.1.1 o0E o0H).1, (o_rec_of repv.2.1.2.1 r1.1 hd.2.1.2.1 o1E o1H).1,
    (o_rec_of repv.2.1.2.2.1 r2.1 hd.2.1.2.2.1 o2E o2H).1,
    (o_rec_of repv.2.1.2.2.2 r3.1 hd.2.1.2.2.2 o3E o3H).1⟩

theorem mem_of {cnt q x : Nat} {T PL : Nat → Nat} (hx : canonK 315 9 (mask 9) (315 * 9) x = true)
    (hT : canonK 315 9 (mask 9) (315 * 9) (T q) = true)
    (h : bAnd(Nat.blt q cnt, Nat.beq (T q) x) = true) :
    memT 315 (hRec 315 9 cnt T PL).1 (tabT (unpack 315 9 x)) = true := by
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  refine memT_of (Nat.le_of_ble_eq_true h1) ?_
  rw [tblEq_unpack hx hT, Nat.eq_of_beq_eq_true h2, Nat.beq_refl]

theorem d_class : (hRec 315 9 J2D.cnt J2D.T J2D.PL).1.all (fun x => tblEq 315 x (idT 315) ||
    j2DReps.any fun r => memT 315
      (conjClosureH 315 j2DGens.toArray (j2DGens.toArray.map (invT 315)) r 100).1 x) = true := by
  unfold j2DReps
  simp only [List.any_cons, List.any_nil, Bool.or_false]
  rw [o_recs.1, o_recs.2.1, o_recs.2.2.1, o_recs.2.2.2, Array.all_eq_true]
  intro i hi
  have hi' : i < J2D.cnt := by simpa [hRec] using hi
  have hx : (hRec 315 9 J2D.cnt J2D.T J2D.PL).1[i]'hi = tabT (unpack 315 9 (J2D.T i)) := by
    simp [hRec]
  rw [hx]
  have hc := allN_spec dIn i hi'
  unfold inClass at hc
  rw [strictB_eq''] at hc
  have hT := canon_of dE i hi'
  simp only [Bool.or_eq_true]
  rcases bIf_or hc with h0 | hc
  · left
    rw [hid, tblEq_unpack hT hidc]
    exact h0
  right
  rcases bIf_or hc with h1 | hc
  · exact Or.inl (mem_of hT (canon_of o0E _ (Nat.le_of_ble_eq_true ((bAnd_iff _ _).1 h1).1)) h1)
  right
  rcases bIf_or hc with h1 | hc
  · exact Or.inl (mem_of hT (canon_of o1E _ (Nat.le_of_ble_eq_true ((bAnd_iff _ _).1 h1).1)) h1)
  right
  rcases bIf_or hc with h1 | h1
  · exact Or.inl (mem_of hT (canon_of o2E _ (Nat.le_of_ble_eq_true ((bAnd_iff _ _).1 h1).1)) h1)
  · exact Or.inr (mem_of hT (canon_of o3E _ (Nat.le_of_ble_eq_true ((bAnd_iff _ _).1 h1).1)) h1)

theorem reps_perm : j2DReps.all (fun c => permOK 315 c) = true := by
  unfold j2DReps
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  rw [r0.1, r1.1, r2.1, r3.1]
  exact ⟨permOK_unpack r0.2 reps_inv.1, permOK_unpack r1.2 reps_inv.2.1,
    permOK_unpack r2.2 reps_inv.2.2.1, permOK_unpack r3.2 reps_inv.2.2.2⟩

theorem reps_all : j2DReps.all (fun r => conjTreeOK 315 j2DGens.toArray
      (j2DGens.toArray.map (invT 315)) r
      (conjClosureH 315 j2DGens.toArray (j2DGens.toArray.map (invT 315)) r 100).1
      (conjClosureH 315 j2DGens.toArray (j2DGens.toArray.map (invT 315)) r 100).2.1
      (conjClosureH 315 j2DGens.toArray (j2DGens.toArray.map (invT 315)) r 100).2.2 &&
    (mulTreeOK 315 (conjClosureH 315 j2DGens.toArray (j2DGens.toArray.map (invT 315)) r 100).1
      (mulClosureH 315 (conjClosureH 315 j2DGens.toArray (j2DGens.toArray.map (invT 315)) r
        100).1 100).1
      (mulClosureH 315 (conjClosureH 315 j2DGens.toArray (j2DGens.toArray.map (invT 315)) r
        100).1 100).2.1
      (mulClosureH 315 (conjClosureH 315 j2DGens.toArray (j2DGens.toArray.map (invT 315)) r
        100).1 100).2.2 &&
      hkeysDistinct 315 (mulClosureH 315 (conjClosureH 315 j2DGens.toArray
        (j2DGens.toArray.map (invT 315)) r 100).1 100).1.toList &&
      (mulClosureH 315 (conjClosureH 315 j2DGens.toArray (j2DGens.toArray.map (invT 315)) r
        100).1 100).1.size == 60)) = true := by
  unfold j2DReps
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [class_ok repv.2.1.1 r0.1 hd.2.1.1 o0E o0H idv.2.1 repv.2.2.1 hd.2.2.1 n0E n0H rfl,
    class_ok repv.2.1.2.1 r1.1 hd.2.1.2.1 o1E o1H idv.2.2.1 repv.2.2.2.1 hd.2.2.2.1 n1E n1H rfl,
    class_ok repv.2.1.2.2.1 r2.1 hd.2.1.2.2.1 o2E o2H idv.2.2.2.1 repv.2.2.2.2.1 hd.2.2.2.2.1 n2E
      n2H rfl,
    class_ok repv.2.1.2.2.2 r3.1 hd.2.1.2.2.2 o3E o3H idv.2.2.2.2 repv.2.2.2.2.2 hd.2.2.2.2.2 n3E
      n3H rfl]
  rfl

theorem dok : j2DOK = true := by
  unfold j2DOK
  simp only [Bool.and_eq_true, beq_iff_eq]
  rw [d_rec]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨d_enum, c1_enum⟩, perms_of c1_tabs (inv_of gens.1.2.2.2.2.1 invs.1)⟩,
    perms_of d_tabs d_invs⟩, reps_perm⟩, d_norm⟩, d_class⟩, reps_all⟩, cent_d⟩

theorem qok : j2QOK = true := by
  unfold j2QOK
  simp only [Bool.and_eq_true, beq_iff_eq]
  exact ⟨⟨⟨⟨⟨q_enum, c2_enum⟩, perms_of c2_tabs (inv_of gens.1.2.2.2.2.2 invs.2.1)⟩,
    perms_of q_tabs (inv_of gens.2.2.2.2.2.2.2 invs.2.2.2.1)⟩, q_norm⟩, cent_q⟩

theorem notcomm :
    commTT 315 (wordTbl 315 j2C1Gens [3, 2]) (wordTbl 315 j2C1Gens [2, 4, 2, 4]) = false := by
  rw [w0, w1, commTT_unpack dg_canon.1 dg_canon.2]
  have h := dNotComm
  unfold pc at h
  cases e : Nat.beq (pcomp 315 9 (mask 9) (J2D.GI 0) (J2D.GI 1))
      (pcomp 315 9 (mask 9) (J2D.GI 1) (J2D.GI 0))
  · rfl
  · rw [e] at h
    exact absurd h (by decide)

theorem facts2280 : (j2DOK = true) ∧ (j2QOK = true) ∧
    (commTT 315 (wordTbl 315 j2C1Gens [3, 2]) (wordTbl 315 j2C1Gens [2, 4, 2, 4]) = false) :=
  ⟨dok, qok, notcomm⟩

end CertificateChecks.KernelSpor.J2Loc

end
