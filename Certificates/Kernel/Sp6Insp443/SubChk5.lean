module

public import Certificates.Data.Kernel.Sp6Insp443.Sub
public import Certificates.Data.Sp6Insp443
public import Certificates.Kernel.Sporadic.Co3.Sp36
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Common.Lce

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelS6I

open CFSG.KC CFSG.KC.Enum CFSG.KS CFSG.KS.Sp6I CFSG.KC.KGC31P CFSG.SectionRank.QTK.Insp443.Sp6
  CertificateChecks.KernelSpor

noncomputable abbrev pT (Ts : List CFSG.Sporadic.Th.Native.Table) : List Nat :=
  Ts.map (packT 6)

theorem ch725106k5 : (cands5.all fun Ts => tabsK 36 6 Ts) = true := by quickRfl

theorem ch725106kd : (ds1.all fun Ts => tabsK 36 6 Ts) = true ∧
    (ds3.all fun Ts => tabsK 36 6 Ts) = true ∧ (ds4.all fun Ts => tabsK 36 6 Ts) = true :=
  ⟨by quickRfl, by quickRfl, by quickRfl⟩

theorem ch725106kh : tabsK 36 6 hs1 = true ∧ tabsK 36 6 hs3 = true ∧ tabsK 36 6 hs4 = true ∧
    tabsK 36 6 [a1T, g1T, h1T] = true ∧ tabsK 36 6 [a3T, g3T, h3T] = true ∧
    tabsK 36 6 [a4T, g4T, h4T] = true :=
  ⟨by quickRfl, by quickRfl, by quickRfl, by quickRfl, by quickRfl, by quickRfl⟩

theorem ch725106f : ([a1T, g1T, h1T, a3T, g3T, h3T, a4T, g4T, h4T].all fun T =>
    Co3Sp36.sift (packT 6 T)) = true := by quickRfl

theorem ch725106e1 : psixE 36 6 (pT (cands5.getD 1 [])) (ds1.map pT) (pT hs1) (packT 6 a1T)
    (packT 6 g1T) (packT 6 h1T) = true := by quickRfl

theorem ch725106e3 : psixE 36 6 (pT (cands5.getD 3 [])) (ds3.map pT) (pT hs3) (packT 6 a3T)
    (packT 6 g3T) (packT 6 h3T) = true := by quickRfl

theorem ch725106e4 : psixE 36 6 (pT (cands5.getD 4 [])) (ds4.map pT) (pT hs4) (packT 6 a4T)
    (packT 6 g4T) (packT 6 h4T) = true := by quickRfl

theorem ch725106b :
    psubOK 36 6 (pT (cands5.getD 0 [])) (pT (cands5.getD 1 [])) = true ∧
    psubOK 36 6 (pT (cands5.getD 1 [])) (pT (cands5.getD 1 [])) = true ∧
    psubOK 36 6 (pT (cands5.getD 2 [])) (pT (cands5.getD 3 [])) = true ∧
    psubOK 36 6 (pT (cands5.getD 3 [])) (pT (cands5.getD 3 [])) = true ∧
    psubOK 36 6 (pT (cands5.getD 4 [])) (pT (cands5.getD 4 [])) = true ∧
    psubOK 36 6 (pT (cands5.getD 5 [])) (pT (cands5.getD 4 [])) = true ∧
    pspanEq 36 6 (pT (cands5.getD 0 [])) (pT (ds1.getD 0 [])) = true ∧
    pspanEq 36 6 (pT (cands5.getD 2 [])) (pT (ds3.getD 0 [])) = true ∧
    pspanEq 36 6 (pT (cands5.getD 5 [])) (pT (ds4.getD 0 [])) = true :=
  ⟨by quickRfl, by quickRfl, by quickRfl, by quickRfl, by quickRfl, by quickRfl, by quickRfl,
    by quickRfl, by quickRfl⟩

end CertificateChecks.KernelS6I

end
