module

public import Certificates.Kernel.SporSch.J1.Count
public import Certificates.Kernel.SporSch.J1.ClassJ
public import Certificates.Kernel.SporSch.J1.ChainCK
public import CFSG.Certificates.Kernel.SporSch.J1PtSound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.J1

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.M11 CFSG.KS.SporSch.MOC
open CFSG.Sporadic.Schreier CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
open CFSG.Monster.B.Mathieu CFSG.Certificates.Native

theorem pA : permOK 3080 12 (mask 12) (3080 * 12) (J1L.S 0) (pinvS 3080 12 (mask 12) (J1L.S 0)) =
    true := by quickRfl

theorem pB : permOK 3080 12 (mask 12) (3080 * 12) (J1L.S 1) (pinvS 3080 12 (mask 12) (J1L.S 1)) =
    true := by quickRfl

theorem cA : canonK 3080 12 (mask 12) (3080 * 12) (J1L.S 0) = true := by quickRfl

theorem cB : canonK 3080 12 (mask 12) (3080 * 12) (J1L.S 1) = true := by quickRfl

theorem oA : ordIs 3080 12 (mask 12) (pidn 3080 12) (J1L.S 0) (2 - 1) = true := by quickRfl

theorem oB : ordIs 3080 12 (mask 12) (pidn 3080 12) (J1L.S 1) (3 - 1) = true := by quickRfl

theorem oAB : ordIs 3080 12 (mask 12) (pidn 3080 12) (pcomp 3080 12 (mask 12) (J1L.S 0) (J1L.S 1))
    (7 - 1) = true := by quickRfl

theorem oC : ordIs 3080 12 (mask 12) (pidn 3080 12) (pcomp 3080 12 (mask 12) (J1L.S 0)
    (pcomp 3080 12 (mask 12) (J1L.S 1) (pcomp 3080 12 (mask 12)
      (powK 3080 12 (mask 12) (pidn 3080 12) (J1L.S 0) (2 - 1))
      (powK 3080 12 (mask 12) (pidn 3080 12) (J1L.S 1) (3 - 1))))) (19 - 1) = true := by
  quickRfl

theorem hd : clsPtHdK 3080 12 (mask 12) (3080 * 12) J1L.BP 3 J1L.LR J1L.TR J1PK.E J1PK.c J1PK.r
    J1PC.jR 2 2000 = true := by
  quickRfl

theorem szJ : szOK 3080 12 = true := by quickRfl

theorem blkJ : Nat.blt (64 * (rcnt (J1L.LR 1) * rcnt (J1L.LR 2))) 1048576 = true := by quickRfl

theorem negBlk : (!(Nat.blt (65536 * (rcnt (J1L.LR 1) * rcnt (J1L.LR 2))) 1048576)) = true := by
  quickRfl

theorem negHdRoot : (!(clsPtHdK 3080 12 (mask 12) (3080 * 12) J1L.BP 3 J1L.LR J1L.TR J1PK.E J1PK.c
    J1PK.r (Nat.succ J1PC.jR) 2 2000)) = true := by
  quickRfl

theorem negHdCap : (!(clsPtHdK 3080 12 (mask 12) (3080 * 12) J1L.BP 3 J1L.LR J1L.TR J1PK.E J1PK.c
    J1PK.r J1PC.jR 2 1462)) = true := by
  quickRfl

theorem negDepth : (!(clsPtK 3080 12 (mask 12) (3080 * 12) J1L.BP 3 (ordK J1L.LR 3) (J1L.S 0)
    (J1L.SI 0) (J1L.S 1) (J1L.SI 1) J1L.LR J1L.TR J1PK.E J1PK.IA J1PK.IB J1PK.PA J1PK.LB
    (fun _ => 0) J1PK.c J1PK.r 1)) = true := by
  quickRfl

theorem negPerm : (!(permOK 3080 12 (mask 12) (3080 * 12) (J1L.S 0) (J1L.S 1))) = true := by
  quickRfl

theorem countFacts : (invOK 3080 j1ATbl j1AInvTbl = true ∧ invOK 3080 j1BTbl j1BInvTbl = true ∧
      ordTest 3080 2 j1ATbl = true ∧ ordTest 3080 3 j1BTbl = true ∧
      pairTest 3080 7 19 2 3 j1ATbl j1BTbl = true
    )
    ∧ ((j1OrderTables 2).length = 1463)
    ∧ ((j1OrderTables 3).length = 5852)
    ∧ (classOK 3080 j1GenTbls j1GenInvTbls (j1OrderTables 2) 2000 = true)
    ∧ (classTotal 3080 j1GenTbls j1GenInvTbls (j1OrderTables 2) (j1OrderTables 3) 2000 7 19 2 3 =
      175560
    ) := by
  obtain ⟨h1, h2, h3, h4⟩ := ptCount_sound (n := 3080) (w := 12) (mx := 2) (my := 3) (r := 7)
    (s := 19) (cap := 2000) chainCK bindA bindB
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩ (L := 64) (CS := J1PC.CS)
    (by decide) (Nat.le_of_ble_eq_true blkJ) J1PC.hc hd
    (elems_of_blocks (by decide) J1PK.hb) (by decide)
  have eA : j1ATbl = listTbl 3080 (j1Chain.generators.getD 0 []) := by rw [j1ATbl, lA_eq]
  have eB : j1BTbl = listTbl 3080 (j1Chain.generators.getD 1 []) := by rw [j1BTbl, lB_eq]
  have eG : j1GenTbls = #[listTbl 3080 (j1Chain.generators.getD 0 []),
      listTbl 3080 (j1Chain.generators.getD 1 [])] := by rw [j1GenTbls, eA, eB]
  have eGi : j1GenInvTbls = #[invT 3080 (listTbl 3080 (j1Chain.generators.getD 0 [])),
      invT 3080 (listTbl 3080 (j1Chain.generators.getD 1 []))] := by
    rw [j1GenInvTbls, j1AInvTbl, j1BInvTbl, eA, eB]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [j1AInvTbl, eA]
    exact invOK_listTbl szJ bindA pA
  · rw [j1BInvTbl, eB]
    exact invOK_listTbl szJ bindB pB
  · rw [eA]
    exact ordTest_listTbl szJ bindA pA cA (by norm_num) oA
  · rw [eB]
    exact ordTest_listTbl szJ bindB pB cB (by norm_num) oB
  · rw [eA, eB]
    exact pairTest_listTbl szJ bindA bindB pA pB (by norm_num) (by norm_num) oAB oC
  · rw [orderTables_eq]
    exact h1.trans (by decide)
  · rw [orderTables_eq]
    exact h2.trans (by decide)
  · rw [orderTables_eq, eG, eGi]
    exact h3
  · rw [orderTables_eq, orderTables_eq, eG, eGi]
    exact h4.trans (by decide)

end CertificateChecks.KernelSporSch.J1

end
