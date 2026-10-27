module

public import Certificates.Kernel.RuThree.K
public import Certificates.Kernel.Misc.RuThreeM10.Checks
public import Certificates.Data.Kernel.HeLoc.TreeTab
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.RuThreeInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelRuThree

open CFSG.EvenSporadicStandard.RuStd.S2

meta def mtM : Array (Array Nat) := Id.run do
  let c := ruThreeC0Cert
  let mut r : Array (Array Nat) := #[]
  for i in [0:c.pts.size] do
    if i == 0 then
      r := r.push (Array.range 11)
    else
      let a := ruThreeM[c.lab[i]!]!
      let u := r[c.par[i]!]!
      r := r.push (Array.ofFn (n := 11) fun x => a[u[x.val]!]!)
  return r

end CertificateChecks.KernelRuThree

#kmisc_packarrs CertificateChecks.KernelRuThree.MT CertificateChecks.KernelRuThree.mtM 4

namespace CertificateChecks.KernelRuThree

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CFSG.KC.HeLoc CFSG.KS.Prim
  CFSG.EvenSporadicStandard.RuStd.S2

@[expose] noncomputable def gM (k x : Nat) : Nat :=
  pg 4 (mask 4) (KernelMisc.RuThreeM10.ET.G k) x

@[expose] noncomputable def rd4 (a x : Nat) : Nat := pg 4 (mask 4) a x

@[expose] def bs11 : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

@[expose] noncomputable def kerAt (m : Nat → Nat → Nat) (i : Nat) : Bool :=
  bIf(eqOnL bs11 (m i) (fun y => y),
    bIf(eqOnL bs (cv i) (fun y => y), true,
      bIf(eqOnL bs (cv i) x0, true, eqOnL bs (cv i) (fun y => x0 (x0 y)))), true)

@[expose] noncomputable def kerAtT (T : Nat → Nat) (i : Nat) : Bool :=
  strictB (T i) fun a => kerAt (fun _ => rd4 a) i

theorem kTabT : allN 2160 (tabAtK gM rd4 MT C0.P C0.L bs11) = true := by quickRfl

theorem kEdgeT : allN 2160 (edgeTK gM rd4 MT CE 2160 3 bs11) = true := by quickRfl

theorem kKerT : allN 2160 (kerAtT MT) = true := by quickRfl

theorem kM0 : eqOnL bs11 (gM 0) (fun y => y) = true := by quickRfl

theorem kTabTNeg :
    (!allN 2160 (tabAtK (fun k => gM (Nat.sub 2 k)) rd4 MT C0.P C0.L bs11)) = true := by
  quickRfl

theorem kEdgeTNeg :
    (!allN 2160 (edgeTK (fun k => gM (Nat.sub 2 k)) rd4 MT CE 2160 3 bs11)) = true := by
  quickRfl

theorem kKerTNeg : (!allN 2160 (kerAtT fun _ => pidn 11 4)) = true := by quickRfl

theorem kM0Neg : (!eqOnL bs11 (gM 1) (fun y => y)) = true := by quickRfl

end CertificateChecks.KernelRuThree

end
