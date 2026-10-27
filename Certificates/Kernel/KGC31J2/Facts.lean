module

public import Certificates.Kernel.KGC31J2.Small
public import Certificates.Kernel.KGC31J2.Cls
public import Certificates.Kernel.KGC31J2.Cnt
public import Certificates.Kernel.KGC31J2.Inv0
public import Certificates.Kernel.KGC31J2.Inv1
public import Certificates.Kernel.KGC31J2.Inv2
public import Certificates.Kernel.KGC31J2.Inv3
public import CFSG.Certificates.Kernel.KGC31PGridSound
public import CFSG.Certificates.Kernel.J2EnumSound
public import CFSG.Certificates.Kernel.J2Enum.ClsMem
public import CFSG.Certificates.Kernel.Common.ForallChunks
public import CFSG.Quasithin.Vol2.KGFactC31J2Data
public import CFSG.Sporadic.Schreier.ImagePairs
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.BfsPinSound
public import CFSG.Certificates.Kernel.HeModelKSound
public import CFSG.Certificates.Kernel.HexaKSound
public import CFSG.Certificates.Kernel.SporSch.MathieuOCSound
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutCheckBase
public import CFSG.Quasithin.Vol2.KGFactC31CosetCheck

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelKGC31J2

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.KGC31P CFSG.KC.Child3 CFSG.KC.J2Enum
open CFSG.KC.BfsPin
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.Schreier.PairNative CFSG.Sporadic.Schreier.PairJ2
open CFSG.Quasithin.KGC31.Native CFSG.Quasithin.KGC31.J2
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.ComponentClassification.J2Cover
open CertificateChecks.KernelSporSch

#kc_forall_chunks c7199InvAll (fun k => invBlk k = true) 15 CertificateChecks.KernelKGC31J2.invBlk 1

theorem hsz : szOK 315 9 = true := by quickRfl

theorem ppS (j : Nat) (hj : j < 7) : PP 315 9 (PJ2.S j) :=
  CFSG.KC.HeGlueK.PP_of_permOK2 hsz (CFSG.KS.Raw.Orb.allN_iff.1 PJ2.perm j hj)

theorem ppG (l : Int) : PP 315 9 (G l) := by
  unfold G
  split
  · exact ppS 0 (by norm_num)
  · exact ppS 1 (by norm_num)

theorem genTab_eq (j : Nat) (hj : j < 7) : genTab j = tabP 315 9 (PJ2.S j) := by
  rw [genTab, tabP, arrTable, PJ2.arr_eq j hj]

theorem gensT_eq (l : Int) : gensT l = tabP 315 9 (G l) := by
  unfold gensT G
  split
  · exact genTab_eq 0 (by norm_num)
  · exact genTab_eq 1 (by norm_num)

theorem wordT_eq (wd : List Int) : wordT 315 gensT wd = tabP 315 9 (pw wd) :=
  wordT_tabP hsz gensT_eq ppG wd

theorem ppw' (wd : List Int) : PP 315 9 (pw wd) := PP_pword hsz ppG wd

theorem strictN_eqJ (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem sumF_congrJ {f g : Nat → Nat} : ∀ m, (∀ a < m, f a = g a) → sumF m f = sumF m g
  | 0, _ => rfl
  | m + 1, h => by
    have e : ∀ r : Nat → Nat, sumF (m + 1) r = sumF m r + r m := fun r => by
      change strictN (sumF m r) (fun s' => Nat.add s' (r m)) = _
      rw [strictN_eqJ]
      rfl
    rw [e, e, sumF_congrJ m fun a ha => h a (by omega), h m (by omega)]

theorem chainJ : ChainOK3 315 9 7 2 PJ2.BP 40 8 PJ2.S PJ2.SI PJ2.LR PJ2.TR PJ2.TRI PJ2Words.D
    (j2StrongArrs ()) baseArr :=
  ⟨PJ2.binds, PJ2.head, PJ2.hl, by norm_num, PJ2.hs, PJ2.perm⟩

theorem levP : rcnt (PJ2.LR 0) = 315 ∧ rcnt (PJ2.LR 1) = 160 ∧ rcnt (PJ2.LR 2) = 12 := by
  have h := kLev
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨a, b⟩, c⟩ := h
  exact ⟨Nat.eq_of_beq_eq_true a, Nat.eq_of_beq_eq_true b, Nat.eq_of_beq_eq_true c⟩

theorem k20 : rcnt (PJ2.LR 0) * rcnt (PJ2.LR 1) * rcnt (PJ2.LR 2) < 2 ^ 20 := by
  rw [levP.1, levP.2.1, levP.2.2]
  norm_num

theorem kRP : (canonK 315 9 (mask 9) (315 * 9) (PJ2.S 0) = true ∧
      siftK 315 9 (mask 9) (315 * 9) (pidn 315 9) PJ2.LR PJ2.TRI PJ2.BP 3 0 (PJ2.S 0) = true) ∧
    (canonK 315 9 (mask 9) (315 * 9) (PJ2.S 1) = true ∧
      siftK 315 9 (mask 9) (315 * 9) (pidn 315 9) PJ2.LR PJ2.TRI PJ2.BP 3 0 (PJ2.S 1) = true) := by
  have h := kR
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨a, b⟩, c⟩, d⟩ := h
  exact ⟨⟨a, b⟩, c, d⟩

theorem sum0 : sumF (rcnt (PJ2.LR 0))
    (blkCnt 315 9 PJ2.LR PJ2.TR PJ2.BP (pidn 315 9) (PJ2.S 0) (PJ2.S 1)) = sumF 315 (lget E0) := by
  rw [levP.1]
  exact sumF_congrJ 315 fun a ha => Nat.eq_of_beq_eq_true
    (CFSG.KC.Co3Bfs.cover_of_blocks (by norm_num) (by norm_num) E0B.all a ha)

theorem hRN : RJ.N = 2835 := Nat.eq_of_beq_eq_true kN

theorem lenInv : invTabs.length = RJ.N := by
  unfold invTabs
  rw [(enumCnt_sound chainJ k20 kRP.1 kRP.2).1, sum0, Nat.eq_of_beq_eq_true kTot, hRN]

theorem hgp : ∀ l < 2, RJ.GP l = PJ2.S l ∧ RJ.GIP l = PJ2.SI l := by
  have h := kGP
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨a, b⟩, c⟩, d⟩ := h
  intro l hl
  interval_cases l
  · exact ⟨Nat.eq_of_beq_eq_true a, Nat.eq_of_beq_eq_true c⟩
  · exact ⟨Nat.eq_of_beq_eq_true b, Nat.eq_of_beq_eq_true d⟩

theorem hCS : RJ.CS.length = 2 := by
  have h := kCS
  simp only [Bool.and_eq_true] at h
  exact Nat.eq_of_beq_eq_true h.1.1

theorem repAll : ∀ i < 2, repOK i = true := by
  intro i hi
  interval_cases i
  · exact kRep0
  · exact kRep1

theorem hrep : ∀ i < RJ.CS.length,
    canonK 315 9 (mask 9) (315 * 9) (RJ.E (lget RJ.OFF i)) = true ∧
      siftK 315 9 (mask 9) (315 * 9) (pidn 315 9) PJ2.LR PJ2.TRI PJ2.BP 3 0
        (RJ.E (lget RJ.OFF i)) = true ∧
      ordTest 315 2 (arrTable 315 (unpack 315 9 (RJ.E (lget RJ.OFF i)))) = true := by
  intro i hi
  have h := repAll i (hCS ▸ hi)
  simp only [repOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨a, b⟩, c⟩, d⟩ := h
  refine ⟨a, b, ?_⟩
  have e := ordTest_tabP (CFSG.KC.HeGlueK.PP_of_permOK2 hsz c) 2
  rw [tabP] at e
  rw [e]
  exact d

theorem recAll : ∀ j < RJ.N, repK 315 9 RJ.GP RJ.GIP 2 RJ.CS RJ.OFF RJ.CI RJ.E RJ.P RJ.L RJ.K RJ.S
    RJ.SI RJ.N 4000 j = true := by
  rw [hRN]
  exact CFSG.KC.Co3Bfs.cover_of_blocks (f := fRJ) (by norm_num) (by norm_num) RJB.all

theorem mem_invs : ∀ t ∈ invTabs, ∃ j < RJ.N, t = tabP 315 9 (RJ.E j) := by
  unfold invTabs
  exact mem_records chainJ le_rfl hgp le_rfl kOff recAll hrep lenInv

theorem invOne_all : ∀ j < RJ.N, invOne j = true := by
  intro j hj
  rw [hRN] at hj
  have hk : j / 200 < 15 := by omega
  apply List.all_eq_true.1 (c7199InvAll (j / 200) hk) j
  rw [List.mem_range'_1, hRN]
  omega

theorem inv_facts {j : Nat} (hj : j < RJ.N) :
    PP 315 9 (RJ.E j) ∧ pactOne 315 9 5 X5a (RJ.E j) = true ∧
      (∀ c < 5, pactOne 315 9 5 (L5 c) (RJ.E j) = true) ∧ pactOne 315 9 7 X7 (RJ.E j) = true := by
  have h := invOne_all j hj
  simp only [invOne, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨CFSG.KC.HeGlueK.PP_of_permOK2 hsz h1, h2,
    fun c hc => List.all_eq_true.1 h3 c (List.mem_range.2 hc), h4⟩

theorem hI : ∀ t ∈ invTabs, ∃ u, PP 315 9 u ∧ t = tabP 315 9 u := by
  intro t ht
  obtain ⟨j, hj, rfl⟩ := mem_invs t ht
  exact ⟨_, (inv_facts hj).1, rfl⟩

theorem ord5a : ordTest 315 5 x5aT = true := by
  rw [x5aT, wordT_eq, ordTest_tabP (ppw' w5a)]
  exact kOrd5a

theorem ord5b : ordTest 315 5 x5bT = true := by
  rw [x5bT, wordT_eq, ordTest_tabP (ppw' w5b)]
  exact kOrd5b

theorem ord7 : ordTest 315 7 x7T = true := by
  rw [x7T, wordT_eq, ordTest_tabP (ppw' w7)]
  exact kOrd7

theorem comm5 : tblEq 315 (compT 315 x5aT x5bT) (compT 315 x5bT x5aT) = true := by
  rw [x5aT, x5bT, wordT_eq, wordT_eq, compT_tabP' (ppw' w5a) (ppw' w5b),
    compT_tabP' (ppw' w5b) (ppw' w5a), tblEq_tabP ((ppw' w5a).pc (ppw' w5b))
      ((ppw' w5b).pc (ppw' w5a))]
  exact kComm

theorem grid5 : gridInj 315 x5aT x5bT 5 = true := by
  rw [x5aT, x5bT, wordT_eq, wordT_eq, gridInj_tabP (ppw' w5a) (ppw' w5b)]
  exact kGrid

theorem act5 : actCheck 315 5 invTabs (gridTabs 315 x5aT x5bT 5 5) = true := by
  rw [x5aT, x5bT, wordT_eq, wordT_eq]
  refine actCheck_gridTabs (ppw' w5a) (ppw' w5b) (by norm_num) kOrd5a kOrd5b kComm ?_
  intro t ht
  obtain ⟨j, hj, rfl⟩ := mem_invs t ht
  obtain ⟨h1, h2, h3, -⟩ := inv_facts hj
  exact ⟨_, h1, rfl, h2, h3⟩

theorem act7 : actCheck 315 7 invTabs (powTabs 315 x7T 7) = true := by
  rw [x7T, wordT_eq, actCheck_powTabs (ppw' w7) (by norm_num) kOrd7 hI, actCheck,
    List.all_cons, List.all_nil, Bool.and_true, invOK_tabP (ppw' w7), Bool.true_and,
    List.all_eq_true]
  intro t ht
  obtain ⟨j, hj, rfl⟩ := mem_invs t ht
  rw [actOne_tabP (ppw' w7) (inv_facts hj).1]
  exact (inv_facts hj).2.2.2

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
  CFSG.Quasithin.KGC31.Native CFSG.Quasithin.KGC31.J2 in
open Certificates in
theorem cert7199 : ordTest 315 5 x5aT = true ∧ ordTest 315 5 x5bT = true ∧ ordTest 315 7 x7T = true ∧
    tblEq 315 (compT 315 x5aT x5bT) (compT 315 x5bT x5aT) = true ∧
    gridInj 315 x5aT x5bT 5 = true ∧
    actCheck 315 5 invTabs (gridTabs 315 x5aT x5bT 5 5) = true ∧
    actCheck 315 7 invTabs (powTabs 315 x7T 7) = true :=
  ⟨ord5a, ord5b, ord7, comm5, grid5, act5, act7⟩

end CertificateChecks.KernelKGC31J2

end
