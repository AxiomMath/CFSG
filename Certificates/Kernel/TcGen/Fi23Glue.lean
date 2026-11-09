module

public import Certificates.Kernel.TcGen.Fi23
public import CFSG.Certificates.Kernel.OpsLayMcertSound
public import CFSG.Certificates.Kernel.OpsLayTabSound
public import Certificates.Kernel.TcGen.F3Glue

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTc

open CFSG.KC.LQT CFSG.KC.OpsLayK CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native
open CFSG.AGLEmbedding.R3 CFSG.Blueprint
open CFSG.KC.OpsLayK.Snd (runL)

namespace Fi23

theorem tab : ∀ v, 2 < v → v < C.N →
    CFSG.KC.OpsLayTab.entF lay.mul (powK lay) C.VT (CFSG.KC.OpsLayTab.keyAt C.KT v) v = true := by
  refine CFSG.KC.OpsLayTab.tab_of_chunksF (m := 140) (k := 16) (by decide) fun i hi => ?_
  interval_cases i
  exacts [tabC0, tabC1, tabC2, tabC3, tabC4, tabC5, tabC6, tabC7, tabC8, tabC9, tabC10, tabC11,
    tabC12, tabC13, tabC14, tabC15, tabC16, tabC17, tabC18, tabC19, tabC20, tabC21, tabC22,
    tabC23, tabC24, tabC25, tabC26, tabC27, tabC28, tabC29, tabC30, tabC31, tabC32, tabC33,
    tabC34, tabC35, tabC36, tabC37, tabC38, tabC39, tabC40, tabC41, tabC42, tabC43, tabC44,
    tabC45, tabC46, tabC47, tabC48, tabC49, tabC50, tabC51, tabC52, tabC53, tabC54, tabC55,
    tabC56, tabC57, tabC58, tabC59, tabC60, tabC61, tabC62, tabC63, tabC64, tabC65, tabC66,
    tabC67, tabC68, tabC69, tabC70, tabC71, tabC72, tabC73, tabC74, tabC75, tabC76, tabC77,
    tabC78, tabC79, tabC80, tabC81, tabC82, tabC83, tabC84, tabC85, tabC86, tabC87, tabC88,
    tabC89, tabC90, tabC91, tabC92, tabC93, tabC94, tabC95, tabC96, tabC97, tabC98, tabC99,
    tabC100, tabC101, tabC102, tabC103, tabC104, tabC105, tabC106, tabC107, tabC108, tabC109,
    tabC110, tabC111, tabC112, tabC113, tabC114, tabC115, tabC116, tabC117, tabC118, tabC119,
    tabC120, tabC121, tabC122, tabC123, tabC124, tabC125, tabC126, tabC127, tabC128, tabC129,
    tabC130, tabC131, tabC132, tabC133, tabC134, tabC135, tabC136, tabC137, tabC138, tabC139]

theorem run_of_symP {prog : List Op} {VS S : List Nat} {I0 IF n : Nat}
    (h : symP prog VS I0 IF S n = true) : runL lay prog (initR lay A B n) = S := by
  unfold symP at h
  simp only [Bool.and_eq_true] at h
  rw [← eq_of_eqL h.1.2, CFSG.KC.OpsLayTab.runL_of_symF tab _ _ _ _ h.1.1, eq_of_eqL h.2]

theorem tcFa_all : ∀ i < 50, tcFa i = true := by
  intro i hi
  interval_cases i
  exacts [tcFa0, tcFa1, tcFa2, tcFa3, tcFa4, tcFa5, tcFa6, tcFa7, tcFa8, tcFa9, tcFa10, tcFa11,
    tcFa12, tcFa13, tcFa14, tcFa15, tcFa16, tcFa17, tcFa18, tcFa19, tcFa20, tcFa21, tcFa22,
    tcFa23, tcFa24, tcFa25, tcFa26, tcFa27, tcFa28, tcFa29, tcFa30, tcFa31, tcFa32, tcFa33,
    tcFa34, tcFa35, tcFa36, tcFa37, tcFa38, tcFa39, tcFa40, tcFa41, tcFa42, tcFa43, tcFa44,
    tcFa45, tcFa46, tcFa47, tcFa48, tcFa49]

theorem cpFa_all : ∀ i < 30, cpFa i = true := by
  intro i hi
  interval_cases i
  exacts [cpFa0, cpFa1, cpFa2, cpFa3, cpFa4, cpFa5, cpFa6, cpFa7, cpFa8, cpFa9, cpFa10, cpFa11,
    cpFa12, cpFa13, cpFa14, cpFa15, cpFa16, cpFa17, cpFa18, cpFa19, cpFa20, cpFa21, cpFa22,
    cpFa23, cpFa24, cpFa25, cpFa26, cpFa27, cpFa28, cpFa29]

theorem tcSplit :
    Fi23Three.tcProg = Fi23Three.tcProg.take 681 ++ derProg 2 Fi23Three.tcSpec.der :=
  eq_of_opsEqB (by decide +kernel)

theorem cpSplit :
    Fi23Three.cpProg = Fi23Three.cpProg.take 667 ++ derProg 2 Fi23Three.cpSpec.der :=
  eq_of_opsEqB (by decide +kernel)

theorem tcAll : tcFs.all (factL lay (T.SL.getD 6 []) Fi23Three.tcNregs) = true :=
  all_of_chunks (m := 50) (k := 5) (by decide +kernel) fun i hi =>
    factsL_of_L1 lay_ok rfl decA decB LA_eq LB_eq (by decide +kernel) (run_of_symP tcSym)
      (K := List.range Fi23Three.tcNregs) (by decide +kernel) (tcFa_all i hi)

theorem cpAll : cpFs.all (factL lay (C.SL.getD 5 []) Fi23Three.cpNregs) = true :=
  all_of_chunks (m := 30) (k := 5) (by decide +kernel) fun i hi =>
    factsL_of_L1 lay_ok rfl decA decB LA_eq LB_eq (by decide +kernel) (run_of_symP cpSym)
      (K := List.range Fi23Three.cpNregs) (by decide +kernel) (cpFa_all i hi)

end Fi23

theorem cert9507 :
    (tcCheck (ops3 253) NativeSporadic.Fi23Seed1 NativeSporadic.Fi23Seed2 Fi23Three.tcNregs
      Fi23Three.tcProg Fi23Three.tcSpec = true) ∧
    (cpCheck (ops3 253) NativeSporadic.Fi23Seed1 NativeSporadic.Fi23Seed2 Fi23Three.cpNregs
      Fi23Three.cpProg Fi23Three.cpSpec = true) ∧ (Fi23Three.cpSpec.noFun = true) :=
  ⟨tc3T_of (mf := 1) Fi23.lay_ok rfl rfl Fi23.decA Fi23.decB Fi23.LA_eq Fi23.LB_eq
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (Fi23.run_of_symP Fi23.tcSym) (Nat.le_of_eq (Nat.one_mul _).symm)
      (factsL_of_der Fi23.lay_ok rfl Fi23.decA Fi23.decB Fi23.LA_eq Fi23.LB_eq
        (av := Fi23Three.tcSpec.actRegs) Fi23.tcSplit
        (by decide +kernel) (Fi23.run_of_symP Fi23.tcSym) (by decide +kernel)
        (TSpec.facts_split _) Fi23.tcAll) Fi23.tcSeeds,
    cp3T_of (mf := 1) Fi23.lay_ok rfl rfl Fi23.decA Fi23.decB Fi23.LA_eq Fi23.LB_eq
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (Fi23.run_of_symP Fi23.cpSym) (Nat.le_of_eq (Nat.one_mul _).symm)
      (factsL_of_der Fi23.lay_ok rfl Fi23.decA Fi23.decB Fi23.LA_eq Fi23.LB_eq
        (av := Fi23Three.cpSpec.actRegs) Fi23.cpSplit
        (by decide +kernel) (Fi23.run_of_symP Fi23.cpSym) (by decide +kernel)
        (CpSpec.facts_split _) Fi23.cpAll) Fi23.cpSeeds,
    by decide +kernel⟩

end CertificateChecks.KernelTc

end
