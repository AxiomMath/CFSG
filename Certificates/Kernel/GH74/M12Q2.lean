module

public import Certificates.Kernel.Sporadic.OddCore.MulHCmd
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Data.Kernel.Spor.MulHQ
public import Certificates.Data.GH74IvkCentM12
meta import Certificates.Data.GH74IvkCentM12
meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelGH74.M12Q2

open CFSG.GH74.Generic.S45.EvSpor Certificates.IvkCent CFSG.Sporadic.SmallOddCore.Native
  CFSG.PSL3Four.Native

meta def idM : Array Nat := idTab 24

meta def gM : Array (Array Nat) := (m12Q2Gens.map natArr).toArray

meta def idsM : Array (Array Nat) := Array.replicate gM.size idM

meta def giM : Array (Array Nat) := gM.map (CFSG.Monster.B.Co2.Native.invCand 24)

meta def xM : Array (Array Nat) := #[natArr m12KaB, natArr m12ZT, natArr m12ST]

meta def recM : Array (Array Nat) := (bfs (fun j t => conjTab 24 idM gM[j]! t) gM.size idM 3000).tabs

meta def clM : Array (Array Nat) := (recM.map fun x => (gM ++ giM).map fun g => comp 24 x g).flatten

end CertificateChecks.KernelGH74.M12Q2

#kmulh CertificateChecks.KernelGH74.Q2 24 5 CertificateChecks.KernelGH74.M12Q2.idsM
  CertificateChecks.KernelGH74.M12Q2.gM CertificateChecks.KernelGH74.M12Q2.idM 3000
#kmisc_packarrs CertificateChecks.KernelGH74.Q2I CertificateChecks.KernelGH74.M12Q2.giM 5
#kmisc_packarrs CertificateChecks.KernelGH74.M12X CertificateChecks.KernelGH74.M12Q2.xM 5
#kfind CertificateChecks.KernelGH74.Q2Cl CertificateChecks.KernelGH74.M12Q2.recM
  CertificateChecks.KernelGH74.M12Q2.clM

namespace CertificateChecks.KernelGH74.M12Q2

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH
open CFSG.GH74.Generic.S45.EvSpor Certificates.IvkCent CFSG.Sporadic.SmallOddCore.Native

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 24 5 (mask 5) p q

@[expose] noncomputable def idK : Nat := pidn 24 5

@[expose] noncomputable def cK (p : Nat) : Bool := canonK 24 5 (mask 5) (24 * 5) p

@[expose] noncomputable def centAt (X : Nat) : Bool :=
  bIf(Nat.beq (pc X (M12X 0)) (pc (M12X 0) X),
    bIf(Nat.beq X idK, true, bIf(Nat.beq X (M12X 1), true, bIf(Nat.beq X (M12X 2), true,
      Nat.beq X (pc (M12X 2) (M12X 1))))), true)

theorem tabs_eq : m12Q2Gens.map natArr = (List.range 5).map (fun j => unpack 24 5 (Q2.GI j)) ∧
    [natArr m12KaB, natArr m12ZT, natArr m12ST] =
      [unpack 24 5 (M12X 0), unpack 24 5 (M12X 1), unpack 24 5 (M12X 2)] := by
  decide +kernel

theorem base_ok : bAnd(szOK 24 5, bAnd(cK idK, bAnd(CFSG.KS.Prim.idK 24 5 (mask 5),
    bAnd(allN 5 (fun j => cK (Q2.GI j)), bAnd(allN 5 (fun j => cK (Q2I j)),
    bAnd(allN 3 (fun j => cK (M12X j)),
    bAnd(allN 5 (fun j => invEqK 24 5 (mask 5) (24 * 5) (Q2.GI j) (Q2I j)),
    bAnd(allN 5 (fun j => Nat.beq (Q2.G j) idK),
    bAnd(Nat.beq Q2.cnt 384, penumHdK idK Q2.cnt 3000 Q2.T Q2.PL))))))))) = true := by
  quickRfl

theorem sE : penumSlK 24 5 (mask 5) (24 * 5) true Q2.G Q2.GI 5 Q2.cnt Q2.T Q2.PL
    Q2.POS Q2.SRT Q2.SRI 0 Q2.cnt = true := by quickRfl

theorem sH : slK Q2.cnt (hsortPtK 24 5 (mask 5) Q2.cnt Q2.T Q2.HS Q2.HSI) 0 Q2.cnt = true := by
  quickRfl

theorem sCl : slK (Nat.mul Q2.cnt 10)
    (findPtK Q2.cnt Q2.T (prodQK 24 5 (mask 5) 10 Q2.T (bothK 5 Q2.GI Q2I)) Q2Cl) 0
    (Nat.mul Q2.cnt 10) = true := by quickRfl

theorem q2_cent : allN Q2.cnt (fun i => centAt (Q2.T i)) = true := by quickRfl

end CertificateChecks.KernelGH74.M12Q2

end
