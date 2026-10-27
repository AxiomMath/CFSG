module

public import Certificates.Kernel.Misc.Perm.HS100.Base
public import Certificates.Kernel.Misc.Perm.HS100.Class3A
public import Certificates.Kernel.Misc.Perm.HS100.S0Data
public import Certificates.Data.Kernel.Misc.PermWit
public import Certificates.Data.Kernel.Misc.PermAdj
public import Certificates.Data.Kernel.Misc.ArrEnum
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.HS100.S0

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.PermWit CFSG.KC.PermAdj
open CFSG.KC.Misc.ArrEnum (permB memK fixK)
open CFSG.KC.LQT.P (anyN)
open CertificateChecks.KernelMisc.HS100

@[expose] noncomputable def Y0 : Nat := SX.F 0

@[expose] noncomputable def U0 : Nat := SX.F 1

@[expose] noncomputable def Z0 : Nat := ZX.F 4

@[expose] noncomputable def cK (p q : Nat) : Bool :=
  Nat.beq (pcomp 100 7 (mask 7) p q) (pcomp 100 7 (mask 7) q p)

@[expose] noncomputable def ord3K (b : Nat) : Bool :=
  Nat.beq (ppow 100 7 (mask 7) (pidn 100 7) b 3) (pidn 100 7) && !(Nat.beq b (pidn 100 7))

@[expose] noncomputable def tableB (fx fu : Nat) (mj oc : Bool) : Bool :=
  (!mj || (Nat.beq fx 20 && Nat.beq fu 0)) &&
    (mj || !oc || (Nat.beq fx 20 && Nat.beq fu 0) || (Nat.beq fx 0 && Nat.beq fu 20)) &&
    (mj || oc || (Nat.beq fx 0 && Nat.beq fu 0))

@[expose] noncomputable def tablePt (i : Nat) : Bool :=
  strictB (AB.T i) fun x =>
    !(invoK 100 7 x) ||
      tableB (fixK 100 7 x) (fixK 100 7 (pcomp 100 7 (mask 7) U0 x)) (memK JJ.N JJ.T x)
        (anyN JJ.N fun j => ord3K (JJ.T j) && cK x (JJ.T j))

@[expose] noncomputable def coxK (S : Nat → Nat) (m : Nat) : Bool :=
  allN m (fun i => Nat.beq (pcomp 100 7 (mask 7) (S i) (S i)) (pidn 100 7)) &&
    allN (m - 1) (fun i => Nat.beq (pcomp 100 7 (mask 7) (pcomp 100 7 (mask 7) (S i) (S (i + 1))) (S i))
      (pcomp 100 7 (mask 7) (pcomp 100 7 (mask 7) (S (i + 1)) (S i)) (S (i + 1)))) &&
    allN m (fun i => allN m (fun j => Nat.blt j (i + 2) || cK (S i) (S j)))

theorem coxXK : coxK (fun i => SX.F (Nat.add 1 i)) 4 = true := by quickRfl

theorem coxRK : coxK (fun i => SX.F (Nat.add 5 i)) 5 = true := by quickRfl

theorem sperm : allN 11 (fun k => permB 100 7 (SX.F k)) = true := by quickRfl

theorem zperm : (permB 100 7 Z0 && allN 4 (fun k => permB 100 7 (EX.F k))) = true := by quickRfl

theorem ssift : (allN 11 (fun k => siftR 100 7 C.LR C.TRI C.BP 5 (SX.F k)) &&
    siftR 100 7 C.LR C.TRI C.BP 5 Z0) = true := by quickRfl

theorem nums : (Nat.beq KK.ng 4 && Nat.beq KK.N 120 && Nat.beq CY.ng 5 && Nat.beq CY.N 360 &&
    Nat.beq AB.ng 6 && Nat.beq AB.N 1440 && Nat.beq CB.ng 7 && Nat.beq CB.N 2880 &&
    Nat.beq JJ.ng 4 && Nat.beq JJ.N 360 && Nat.beq E0.ng 4 && Nat.beq E0.N 16 &&
    Nat.beq ZO.ng 2 && Nat.beq ZO.N 5775 && Nat.beq UO.ng 2 && Nat.beq UO.N 15400 &&
    Nat.beq ZO.r0 0 && Nat.beq UO.r0 0) = true := by quickRfl

theorem binds : (allN 4 (fun k => Nat.beq (KK.G k) (SX.F (Nat.add 1 k))) &&
    allN 5 (fun k => Nat.beq (CY.G k) (SX.F k)) &&
    allN 6 (fun k => Nat.beq (AB.G k) (SX.F (Nat.add 5 k))) &&
    Nat.beq (CB.G 0) (SX.F 1) && allN 6 (fun k => Nat.beq (CB.G (Nat.succ k)) (SX.F (Nat.add 5 k))) &&
    allN 4 (fun k => Nat.beq (JJ.G k) (pcomp 100 7 (mask 7) (SX.F (Nat.add 5 k)) (SX.F (Nat.add 6 k)))) &&
    allN 4 (fun k => Nat.beq (E0.G k) (EX.F k)) &&
    allN 2 (fun k => Nat.beq (ZO.G k) (HX.F k)) && allN 2 (fun k => Nat.beq (UO.G k) (HX.F k)) &&
    Nat.beq (ZO.T ZO.r0) Z0 && Nat.beq (UO.T UO.r0) U0 && Nat.beq (K3.T K3.r1) Y0) = true := by
  quickRfl

theorem keysAll : (keysSK 100 7 CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S0.keys KK.N KK.T
      ((List.range 120).map KKK) &&
    keysSK 100 7 CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S0.keys CY.N CY.T
      ((List.range 360).map CYK) &&
    keysSK 100 7 CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S0.keys AB.N AB.T
      ((List.range 1440).map ABK) &&
    keysSK 100 7 CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S0.keys CB.N CB.T
      ((List.range 2880).map CBK) &&
    keysSK 100 7 CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S0.keys JJ.N JJ.T
      ((List.range 360).map JJK)) = true := by quickRfl

theorem prods : (Nat.beq (pcomp 100 7 (mask 7) Z0 Z0) (pidn 100 7) && !(Nat.beq Z0 (pidn 100 7)) &&
    !(Nat.beq U0 (pidn 100 7)) && Nat.beq (ppow 100 7 (mask 7) (pidn 100 7) Y0 3) (pidn 100 7) &&
    !(Nat.beq Y0 (pidn 100 7)) && cK Y0 Z0 &&
    !(Nat.beq (pcomp 100 7 (mask 7) (SX.F 1) (SX.F 2)) (pidn 100 7)) &&
    !(Nat.beq (pcomp 100 7 (mask 7) (SX.F 5) (SX.F 6)) (pidn 100 7)) &&
    allN 4 (fun k => cK Y0 (SX.F (Nat.add 1 k))) && allN 6 (fun k => cK U0 (SX.F (Nat.add 5 k))) &&
    Nat.beq (fixK 100 7 Z0) 20 && Nat.beq (fixK 100 7 U0) 0) = true := by quickRfl

theorem mems : (allN 4 (fun k => memK E0.N E0.T
      (CFSG.KC.ConjOrb.pconj 100 7 (mask 7) Y0 (pinvS 100 7 (mask 7) Y0) (EX.F k))) &&
    memK E0.N E0.T Z0 &&
    Nat.beq (cntK E0.N fun i => cK Y0 (E0.T i)) 4 &&
    !(memK KK.N KK.T Y0) && !(memK AB.N AB.T U0) && memK JJ.N JJ.T Y0 &&
    allN 6 (fun g => allN 4 (fun k => memK JJ.N JJ.T
      (CFSG.KC.ConjOrb.pconj 100 7 (mask 7) (SX.F (Nat.add 5 g)) (pinvS 100 7 (mask 7) (SX.F (Nat.add 5 g)))
        (JJ.G k))))) = true := by quickRfl

theorem cyAll : allN CY.N (fun i => !(allN 4 fun k => cK (CY.T i) (JJ.G k)) ||
    Nat.beq (CY.T i) (pidn 100 7) || Nat.beq (CY.T i) U0) = true := by quickRfl

theorem table : allN AB.N tablePt = true := by quickRfl

end CertificateChecks.KernelMisc.HS100.S0

end
