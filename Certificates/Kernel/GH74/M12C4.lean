module

public import Certificates.Kernel.Sporadic.OddCore.MulHCmd
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Data.Kernel.Spor.MulHQ
public import Certificates.Data.GH74EvSporCheck
meta import Certificates.Data.GH74EvSporCheck
meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelGH74.M12C4

open CFSG.GH74.Generic.S45.EvSpor CFSG.Sporadic.SmallOddCore.Native CFSG.PSL3Four.Native

meta def idM : Array Nat := idTab 24
meta def invM (a : Array Nat) : Array Nat := CFSG.Monster.B.Co2.Native.invCand 24 a

meta def cM : Array (Array Nat) := (m12CGens.map natArr).toArray
meta def hM : Array (Array Nat) := cM.extract 0 3
meta def kM : Array (Array Nat) := (m12KaGens.map natArr).toArray
meta def ids4M : Array (Array Nat) := Array.replicate 4 idM
meta def ids3M : Array (Array Nat) := Array.replicate 3 idM
meta def ids2M : Array (Array Nat) := Array.replicate 2 idM
meta def ciM : Array (Array Nat) := cM.map invM
meta def hiM : Array (Array Nat) := hM.map invM
meta def kiM : Array (Array Nat) := kM.map invM

meta def yM : Array (Array Nat) := #[natArr m12ZT, natArr m12AT, natArr m12ST, natArr m12KaB]

meta def recOf (gs : Array (Array Nat)) : Array (Array Nat) :=
  (bfs (fun j t => conjTab 24 idM gs[j]! t) gs.size idM 3000).tabs
meta def clOf (gs : Array (Array Nat)) : Array (Array Nat) :=
  ((recOf gs).map fun x => (gs ++ gs.map invM).map fun g => comp 24 x g).flatten
meta def c4RecM : Array (Array Nat) := recOf cM
meta def h3RecM : Array (Array Nat) := recOf hM
meta def kaRecM : Array (Array Nat) := recOf kM
meta def c4ClM : Array (Array Nat) := clOf cM
meta def h3ClM : Array (Array Nat) := clOf hM
meta def kaClM : Array (Array Nat) := clOf kM

meta def c4QM : Array (Array Nat) := #[natArr m12AT, natArr m12KaB]

meta def kaQM : Array (Array Nat) :=
  ((List.range 3).toArray.map fun j => #[natArr m12AT, natArr m12KaB].map fun k =>
    comp 24 (comp 24 hM[j]! k) (invM hM[j]!)).flatten ++
  ((List.range 3).toArray.map fun i => (List.range 3).toArray.map fun j =>
    comp 24 (comp 24 hM[i]! hM[j]!) (comp 24 (invM hM[i]!) (invM hM[j]!))).flatten

end CertificateChecks.KernelGH74.M12C4

#kmulh CertificateChecks.KernelGH74.C4 24 5 CertificateChecks.KernelGH74.M12C4.ids4M
  CertificateChecks.KernelGH74.M12C4.cM CertificateChecks.KernelGH74.M12C4.idM 3000
#kmulh CertificateChecks.KernelGH74.H3 24 5 CertificateChecks.KernelGH74.M12C4.ids3M
  CertificateChecks.KernelGH74.M12C4.hM CertificateChecks.KernelGH74.M12C4.idM 3000
#kmulh CertificateChecks.KernelGH74.KA 24 5 CertificateChecks.KernelGH74.M12C4.ids2M
  CertificateChecks.KernelGH74.M12C4.kM CertificateChecks.KernelGH74.M12C4.idM 3000
#kmisc_packarrs CertificateChecks.KernelGH74.C4I CertificateChecks.KernelGH74.M12C4.ciM 5
#kmisc_packarrs CertificateChecks.KernelGH74.H3I CertificateChecks.KernelGH74.M12C4.hiM 5
#kmisc_packarrs CertificateChecks.KernelGH74.KAI CertificateChecks.KernelGH74.M12C4.kiM 5
#kmisc_packarrs CertificateChecks.KernelGH74.M12Y CertificateChecks.KernelGH74.M12C4.yM 5
#kfind CertificateChecks.KernelGH74.C4Cl CertificateChecks.KernelGH74.M12C4.c4RecM
  CertificateChecks.KernelGH74.M12C4.c4ClM
#kfind CertificateChecks.KernelGH74.H3Cl CertificateChecks.KernelGH74.M12C4.h3RecM
  CertificateChecks.KernelGH74.M12C4.h3ClM
#kfind CertificateChecks.KernelGH74.KACl CertificateChecks.KernelGH74.M12C4.kaRecM
  CertificateChecks.KernelGH74.M12C4.kaClM
#kfind CertificateChecks.KernelGH74.C4P CertificateChecks.KernelGH74.M12C4.c4RecM
  CertificateChecks.KernelGH74.M12C4.c4QM
#kfind CertificateChecks.KernelGH74.KAP CertificateChecks.KernelGH74.M12C4.kaRecM
  CertificateChecks.KernelGH74.M12C4.kaQM

namespace CertificateChecks.KernelGH74.M12C4

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH
open CFSG.GH74.Generic.S45.EvSpor CFSG.Sporadic.SmallOddCore.Native

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 24 5 (mask 5) p q

@[expose] noncomputable def idK : Nat := pidn 24 5

@[expose] noncomputable def cK (p : Nat) : Bool := canonK 24 5 (mask 5) (24 * 5) p

@[expose] noncomputable def iK (p q : Nat) : Bool := invEqK 24 5 (mask 5) (24 * 5) p q

@[expose] noncomputable def bIfN (c : Bool) (a b : Nat) : Nat := nIf(c, a, b)

@[expose] noncomputable def kaQ (c : Nat) : Nat :=
  bIfN (Nat.blt c 6)
    (pc (pc (H3.GI (Nat.div c 2)) (bIfN (Nat.beq (Nat.mod c 2) 0) (M12Y 1) (M12Y 3)))
      (H3I (Nat.div c 2)))
    (pc (pc (H3.GI (Nat.div (Nat.sub c 6) 3)) (H3.GI (Nat.mod (Nat.sub c 6) 3)))
      (pc (H3I (Nat.div (Nat.sub c 6) 3)) (H3I (Nat.mod (Nat.sub c 6) 3))))

theorem tabs_eq : m12CGens.map natArr = (List.range 4).map (fun j => unpack 24 5 (C4.GI j)) ∧
    m12KaGens.map natArr = (List.range 2).map (fun j => unpack 24 5 (KA.GI j)) ∧
    [natArr m12ZT, natArr m12AT, natArr m12ST, natArr m12KaB] =
      [unpack 24 5 (M12Y 0), unpack 24 5 (M12Y 1), unpack 24 5 (M12Y 2), unpack 24 5 (M12Y 3)] := by
  decide +kernel

theorem base_ok : bAnd(szOK 24 5, bAnd(cK idK, bAnd(CFSG.KS.Prim.idK 24 5 (mask 5),
    bAnd(allN 4 (fun j => bAnd(cK (C4.GI j), bAnd(cK (C4I j), bAnd(iK (C4.GI j) (C4I j),
      Nat.beq (C4.G j) idK)))),
    bAnd(allN 3 (fun j => bAnd(Nat.beq (H3.GI j) (C4.GI j), bAnd(Nat.beq (H3I j) (C4I j),
      Nat.beq (H3.G j) idK))),
    bAnd(allN 2 (fun j => bAnd(cK (KA.GI j), bAnd(cK (KAI j), bAnd(iK (KA.GI j) (KAI j),
      Nat.beq (KA.G j) idK)))),
    bAnd(allN 3 (fun j => bAnd(cK (M12Y j), iK (M12Y j) (M12Y j))), bAnd(cK (M12Y 3),
    bAnd(Nat.beq C4.cnt 480, bAnd(Nat.beq H3.cnt 240, bAnd(Nat.beq KA.cnt 60,
    bAnd(penumHdK idK C4.cnt 3000 C4.T C4.PL, bAnd(penumHdK idK H3.cnt 3000 H3.T H3.PL,
      penumHdK idK KA.cnt 3000 KA.T KA.PL))))))))))))) = true := by
  quickRfl

theorem facts_ok : bAnd(allN 3 (fun j => bAnd(Nat.beq (pc (M12Y j) (M12Y j)) idK,
      bIf(Nat.beq (M12Y j) idK, false, true))),
    bAnd(Nat.beq (pc (M12Y 2) (M12Y 0)) (pc (M12Y 0) (M12Y 2)),
    bAnd(Nat.beq (pc (M12Y 2) (M12Y 1)) (pc (M12Y 1) (M12Y 2)),
    bAnd(Nat.beq (pc (M12Y 2) (M12Y 3)) (pc (M12Y 3) (M12Y 2)),
    bAnd(Nat.blt (r32 C4P 0) C4.cnt, bAnd(Nat.beq (C4.T (r32 C4P 0)) (M12Y 1),
    bAnd(Nat.blt (r32 C4P 1) C4.cnt, bAnd(Nat.beq (C4.T (r32 C4P 1)) (M12Y 3),
      allN 15 (fun c => bAnd(Nat.blt (r32 KAP c) KA.cnt, Nat.beq (KA.T (r32 KAP c)) (kaQ c)))))))))))
    = true := by
  quickRfl

theorem c4E : penumSlK 24 5 (mask 5) (24 * 5) true C4.G C4.GI 4 C4.cnt C4.T C4.PL
    C4.POS C4.SRT C4.SRI 0 C4.cnt = true := by quickRfl
theorem c4H : slK C4.cnt (hsortPtK 24 5 (mask 5) C4.cnt C4.T C4.HS C4.HSI) 0 C4.cnt = true := by
  quickRfl
theorem c4Cl : slK (Nat.mul C4.cnt 8)
    (findPtK C4.cnt C4.T (prodQK 24 5 (mask 5) 8 C4.T (bothK 4 C4.GI C4I)) C4Cl) 0
    (Nat.mul C4.cnt 8) = true := by quickRfl

theorem h3E : penumSlK 24 5 (mask 5) (24 * 5) true H3.G H3.GI 3 H3.cnt H3.T H3.PL
    H3.POS H3.SRT H3.SRI 0 H3.cnt = true := by quickRfl
theorem h3H : slK H3.cnt (hsortPtK 24 5 (mask 5) H3.cnt H3.T H3.HS H3.HSI) 0 H3.cnt = true := by
  quickRfl
theorem h3Cl : slK (Nat.mul H3.cnt 6)
    (findPtK H3.cnt H3.T (prodQK 24 5 (mask 5) 6 H3.T (bothK 3 H3.GI H3I)) H3Cl) 0
    (Nat.mul H3.cnt 6) = true := by quickRfl

theorem kaE : penumSlK 24 5 (mask 5) (24 * 5) true KA.G KA.GI 2 KA.cnt KA.T KA.PL
    KA.POS KA.SRT KA.SRI 0 KA.cnt = true := by quickRfl
theorem kaH : slK KA.cnt (hsortPtK 24 5 (mask 5) KA.cnt KA.T KA.HS KA.HSI) 0 KA.cnt = true := by
  quickRfl
theorem kaCl : slK (Nat.mul KA.cnt 4)
    (findPtK KA.cnt KA.T (prodQK 24 5 (mask 5) 4 KA.T (bothK 2 KA.GI KAI)) KACl) 0
    (Nat.mul KA.cnt 4) = true := by quickRfl

theorem tabsH_eq : (m12CGens.take 3).map natArr =
    (List.range 3).map (fun j => unpack 24 5 (H3.GI j)) := by
  decide +kernel

theorem h3_inner : allN H3.cnt (fun i => Nat.blt (pg 5 (mask 5) (H3.T i) 0) 12) = true := by
  quickRfl

theorem c4_inner : Nat.beq (cntBelowK C4.cnt (fun i => Nat.blt (pg 5 (mask 5) (C4.T i) 0) 12) 8)
    240 = true := by quickRfl

end CertificateChecks.KernelGH74.M12C4

end
