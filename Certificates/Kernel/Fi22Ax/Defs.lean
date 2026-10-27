module

public import Certificates.Kernel.Sporadic.Fi22.E2067
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelAutXPermCheck
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelAutXPermCheck
public meta import CFSG.Sporadic.FischerOddCore.Fi22Ext
public import CFSG.Sporadic.FischerOddCore.Fi22Ext
public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.Load

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22Ax

meta def btM : Array (Array Nat) :=
  let G := (Array.range 10).map fun k => CFSG.Sporadic.FischerOddCore.fi22ExtArr (11 + k)
  let Gi := G.map (CFSG.Monster.B.Co2.Native.invCand 3510)
  CFSG.EvenSporadicStandard.TwoFi22.DS81.axBasWords.map
    (CFSG.EvenSporadicStandard.TwoFi22.DS81.axWordTab G Gi)

end CertificateChecks.KernelFi22Ax

#kc_items CertificateChecks.KernelFi22Ax.BT include_bytes "data/Defs.BT.items" 52690 2431277424285080252

namespace CertificateChecks.KernelFi22Ax

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CertificateChecks.KernelSpor

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 3510 12 (mask 12) p q

@[expose] noncomputable def axLetK (l : Nat × Bool) : Nat :=
  if l.2 then Fi22E2067.EI (11 + l.1) else Fi22ExtT.L (11 + l.1)

@[expose] noncomputable def axWordK (w : List (Nat × Bool)) : Nat :=
  w.foldr (fun l acc => pc (axLetK l) acc) (pidn 3510 12)

@[expose] noncomputable def axPhiK (m : Nat) : Nat :=
  (List.range 10).foldr (fun i P => if m.testBit i then pc (BT i) P else P) (pidn 3510 12)

@[expose] noncomputable def axImgK (m : Nat) : Nat :=
  (List.range 10).foldr (fun i x => if m.testBit i then pg 12 (mask 12) (BT i) x else x) 0

@[expose] noncomputable def cn (p : Nat) : Bool := canonK 3510 12 (mask 12) (3510 * 12) p

@[expose] noncomputable def axConjSl (k : Nat) : Bool :=
  allN 10 fun i => Nat.beq (pc (Fi22ExtT.L (11 + k)) (BT i))
    (pc (axPhiK (CFSG.EvenSporadicStandard.TwoFi22.DS81.axGc[k]!)[i]!) (Fi22ExtT.L (11 + k)))

end CertificateChecks.KernelFi22Ax

end
