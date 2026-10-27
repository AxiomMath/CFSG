module

public import Certificates.Kernel.LocalComp.Q47Pack
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CertificateChecks.KernelLC.Q47

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.HexaK CFSG.KC.HeAutK CFSG.KC.Q47K
open CFSG.ComponentClassification.AS81.Q47 CFSG.ComponentClassification.AS81.HeSylow
open CertificateChecks.KernelLC CertificateChecks.KernelLC.Step44Check

theorem kDT : directTransG q47D = true := by quickRfl

theorem kDR : directRefG q47D = true := by quickRfl

theorem kDM : directMatG q47D = true := by quickRfl

theorem kDM16 : modelDirectG q47D q47M16 = true := by quickRfl

theorem kDM32 : modelDirectG q47D q47M32 = true := by quickRfl

theorem kT : (allN 6 fun k => Nat.beq (q47Trans[k]!).length (SZ k) &&
    bndK 64 7 q47Trans[k]! (TR k)) = true := by quickRfl

theorem kBnd : (bndK 64 7 q47U1Gens (PK q47U1Gens 7) && bndK 64 7 q47U2Gens (PK q47U2Gens 7) &&
    bndK 64 7 q47G1 (PK q47G1 7) && bndK 64 7 q47G2 (PK q47G2 7)) = true := by quickRfl

theorem kPins : (bindL q47YGens 64 7 Q47Y.ng Q47Y.G && gensP 64 7 Q47Y.ng Q47Y.G &&
    bindL q47NGens 64 7 Q47N.ng Q47N.G && gensP 64 7 Q47N.ng Q47N.G &&
    bindL (q47U1Gens ++ q47YGens) 64 7 Q47UY1.ng Q47UY1.G && gensP 64 7 Q47UY1.ng Q47UY1.G &&
    bindL (q47U2Gens ++ q47YGens) 64 7 Q47UY2.ng Q47UY2.G && gensP 64 7 Q47UY2.ng Q47UY2.G &&
    bindL q47NE32 32 6 Q47NE.ng Q47NE.G && gensP 32 6 Q47NE.ng Q47NE.G) = true := by quickRfl

theorem kRun : (Nat.beq (runK 64 7 2 Q47Y.G 200).length 168 &&
    Nat.beq (runK 64 7 3 (PK q47U1Gens 7) 100).length 8 &&
    Nat.beq (runK 64 7 3 (PK q47U2Gens 7) 100).length 8) = true := by quickRfl

theorem kMP : ((allN 168 fun i => matOf 3 (MPY i) == q47YMat[i]!) &&
    allN 336 fun i => matOf 2 (MPN i) == q47NMat[i]!) = true := by quickRfl

theorem kRef : refPK (runK 64 7 2 Q47Y.G 200) Q47Y.G (PK q47U1Gens 7) (PK q47U2Gens 7)
    (runK 64 7 3 (PK q47U1Gens 7) 100) (runK 64 7 3 (PK q47U2Gens 7) 100) Q47N.G Q47N.N Q47N.T
    q47W1 q47W2 q47Orb q47OrbRep q47L30 = true := by quickRfl

theorem kWit : witsK Q47Y.G (PK q47G1 7) (PK q47G2 7) (runK 64 7 3 (PK q47U1Gens 7) 100)
    (runK 64 7 3 (PK q47U2Gens 7) 100) q47Wit = true := by quickRfl

theorem kHead : (tableHeadK Q47Y.N Q47Y.T MPY 3 (· == [1, 0, 0, 0, 1, 0, 0, 0, 1]) &&
    tableHeadK Q47N.N Q47N.T MPN 2 (fun m => m[1]! == 0 && m[2]! == 0 && m[0]! == m[3]!)) = true := by
  quickRfl

theorem kAdd : ((List.range 6).all (fun k => allN (SZ k) fun j => addK (TR k j)) &&
    allN 2 (fun k => addK (Q47Y.G k) && addK (Q47N.G k)) &&
    allN 3 (fun k => addK (PK q47U1Gens 7 k) && addK (PK q47U2Gens 7 k)) &&
    allN 4 (fun k => addK (PK q47G1 7 k) && addK (PK q47G2 7 k) && addK (K16.CP k) &&
      addK (K32.CP k))) = true := by quickRfl

theorem kBC : bcK BC = true := by quickRfl

theorem kB16 : (bndK 16 5 q47Rep16 K16.REP &&
    (Nat.beq heSylZ16.size 16 && bindListFromK heSylZ16.toList 5 K16.PZ 0) &&
    permOK 16 5 (mask 5) (16 * 5) K16.PZ (pinvS 16 5 (mask 5) K16.PZ) &&
    bndK 64 7 q47D16 K16.GD && bndK 64 7 q47Eb16 K16.GEb && bndK 64 7 q47Fb16 K16.GFb &&
    (allN 4 fun i => bndK 64 7 (kListG q47M16 i) (K16.GK i)) && bndK 64 7 q47C16 K16.CP) = true := by
  quickRfl

theorem kB32 : (bndK 32 6 q47Rep32 K32.REP &&
    (Nat.beq heAutZ32.size 32 && bindListFromK heAutZ32.toList 6 K32.PZ 0) &&
    permOK 32 6 (mask 6) (32 * 6) K32.PZ (pinvS 32 6 (mask 6) K32.PZ) &&
    bndK 64 7 q47D32 K32.GD && bndK 64 7 q47Eb32 K32.GEb && bndK 64 7 q47Fb32 K32.GFb &&
    (allN 4 fun i => bndK 64 7 (kListG q47M32 i) (K32.GK i)) && bndK 64 7 q47C32 K32.CP) = true := by
  quickRfl

theorem kRuns16 : runsB q47M16 K16 = true := by quickRfl

theorem kRuns32 : runsB q47M32 K32 = true := by quickRfl

theorem kRep16 : repK 16 5 K16.REP K16.NQ K16.TQ K16.PZ q47Form = true := by quickRfl

theorem kRep32 : repK 32 6 K32.REP K32.NQ K32.TQ K32.PZ q47Form = true := by quickRfl

theorem kImg16 : (imgK 16 5 K16.REP K16.PZ q47M16.ne.length K16.GNE K16.GD &&
    imgK 16 5 K16.REP K16.PZ q47M16.eg.length K16.GE K16.GEb &&
    imgK 16 5 K16.REP K16.PZ q47M16.fg.length K16.GF K16.GFb) = true := by quickRfl

theorem kImg32 : (imgK 32 6 K32.REP K32.PZ q47M32.ne.length K32.GNE K32.GD &&
    imgK 32 6 K32.REP K32.PZ q47M32.eg.length K32.GE K32.GEb &&
    imgK 32 6 K32.REP K32.PZ q47M32.fg.length K32.GF K32.GFb) = true := by quickRfl

theorem kModel16 : modelB 16 5 q47M16 K16 Q47Y.G = true := by quickRfl

theorem kModel32 : modelB 32 6 q47M32 K32 Q47Y.G = true := by quickRfl

end CertificateChecks.KernelLC.Q47

end
