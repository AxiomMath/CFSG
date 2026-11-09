module

public import Certificates.Data.Kernel.J2Max76Pack
public import Certificates.Kernel.J2Max76.Data
public import Certificates.Kernel.J2Max76.DataP
public import Certificates.Kernel.J2Max76.DataM
public import Certificates.Data.Kernel.MonsterB.BfsReplayT
import all Mathlib.Data.List.Sort
import all Init.Data.Array.Basic

public section

namespace CertificateChecks.J2Max76

open Certificates.K76J2Max Certificates.G2ThreeMax CFSG.Monster.B.TwoA.Census CFSG.KC.J2Max76
  CFSG.KC.Bfs CertificateChecks.KernelJ2Max76

theorem root_lit : (root () == rootLit) = true := by decide +kernel

theorem gens_lit : gensOK gensL = true := by decide +kernel

theorem orb_replay : replayTOK (rdT orbEdgesP 9 5) (lane orbParP 9) (lane orbLabP 9) 5 280 = true := by
  decide +kernel

theorem orb_pl : (orbLit.par.size == 280 && orbLit.lab.size == 280 && lane orbParP 9 0 == 0 &&
    lane orbLabP 9 0 == 0) = true := by decide +kernel

theorem orb_pin : certPin orbLit 280 315 5 orbPtsP orbEdgesP orbParP orbLabP = true := by
  decide +kernel

theorem gens_pinM : pinT gensImgP 9 315 (gensArr.toList.map Array.toList) = true := by
  decide +kernel

theorem orb_okA : natCertA (imgMem gensImgP orbMemP) 5 (fun u => decide (u < 2 ^ 315)) rootLit 280
    (lane orbPtsP 315) (rdT orbEdgesP 9 5) (rszR 280 5) (lane orbParP 9) (lane orbLabP 9)
    (fun i => lane orbPtsP 315 i == memCode orbMemP i) orbLit.pts.toList = true := by
  decide +kernel

theorem orb_size : (orbLit.pts.size == 280) = true := by decide +kernel

theorem orb_fix : ((List.range 3).all fun s => tabOf orbLit (s + 2) 0 == 0) = true := by
  decide +kernel

theorem tabs_pin : (nTabsL.size == 3 && pinT nTabsP 9 280 (nTabsL.toList.map Array.toList)) = true := by
  decide +kernel

theorem tabs_lit : ([permL (tabR orbEdgesP) 280 [2], permL (tabR orbEdgesP) 280 [3],
    permL (tabR orbEdgesP) 280 [4]] == nTabsL.toList.map Array.toList) = true := by
  decide +kernel

theorem orbs_lit : orbsEqB (orbitSearchB (lookB orbsLit fun i => natBfsL (hR nTabsP) 3 i 280) 280)
    orbsLit = true := by
  decide +kernel

theorem o0_replay : replayTOK (rdT o0EdgesP 9 3) (lane o0ParP 9) (lane o0LabP 9) 3 1 = true := by
  decide +kernel

theorem o0_pl : (o0.par.size == 1 && o0.lab.size == 1 && lane o0ParP 9 0 == 0 &&
    lane o0LabP 9 0 == 0) = true := by decide +kernel

theorem o1_replay :
    replayTOK (rdT o1EdgesP 9 3) (lane o1ParP 9) (lane o1LabP 9) 3 135 = true := by
  decide +kernel

theorem o1_pl : (o1.par.size == 135 && o1.lab.size == 135 && lane o1ParP 9 0 == 0 &&
    lane o1LabP 9 0 == 0) = true := by decide +kernel

theorem o15_replay :
    replayTOK (rdT o15EdgesP 9 3) (lane o15ParP 9) (lane o15LabP 9) 3 36 = true := by
  decide +kernel

theorem o15_pl : (o15.par.size == 36 && o15.lab.size == 36 && lane o15ParP 9 0 == 0 &&
    lane o15LabP 9 0 == 0) = true := by decide +kernel

theorem o18_replay :
    replayTOK (rdT o18EdgesP 9 3) (lane o18ParP 9) (lane o18LabP 9) 3 108 = true := by
  decide +kernel

theorem o18_pl : (o18.par.size == 108 && o18.lab.size == 108 && lane o18ParP 9 0 == 0 &&
    lane o18LabP 9 0 == 0) = true := by decide +kernel

theorem o0_pin : certPin o0 1 9 3 o0PtsP o0EdgesP o0ParP o0LabP = true := by decide +kernel

theorem o0_ok : natCertP (hR nTabsP) 3 (fun u => decide (u < 280)) 0 1 9 3 o0PtsP o0EdgesP o0ParP
    o0LabP o0.pts.toList = true := by decide +kernel

theorem o1_pin : certPin o1 135 9 3 o1PtsP o1EdgesP o1ParP o1LabP = true := by decide +kernel

theorem o1_ok : natCertP (hR nTabsP) 3 (fun u => decide (u < 280)) 1 135 9 3 o1PtsP o1EdgesP
    o1ParP o1LabP o1.pts.toList = true := by decide +kernel

theorem o15_pin : certPin o15 36 9 3 o15PtsP o15EdgesP o15ParP o15LabP = true := by decide +kernel

theorem o15_ok : natCertP (hR nTabsP) 3 (fun u => decide (u < 280)) 15 36 9 3 o15PtsP o15EdgesP
    o15ParP o15LabP o15.pts.toList = true := by decide +kernel

theorem o18_pin : certPin o18 108 9 3 o18PtsP o18EdgesP o18ParP o18LabP = true := by
  decide +kernel

theorem o18_ok : natCertP (hR nTabsP) 3 (fun u => decide (u < 280)) 18 108 9 3 o18PtsP o18EdgesP
    o18ParP o18LabP o18.pts.toList = true := by decide +kernel

theorem orbs_cover :
    ((orbsLit.flatMap fun t => t.2.pts.toList).insertionSort (· ≤ ·) == List.range 280) = true := by
  decide +kernel

theorem w1_lit : (pathWord orbLit 280 1 == w1) = true := by decide +kernel

theorem rp1_pin : pin1 9 rp1.toList rp1P = true := by decide +kernel

theorem rp1_lit : (permL (tabR orbEdgesP) 280 w1 == rp1.toList) = true := by decide +kernel

theorem c1_replay : replayTOK (rdT c1EdgesP 9 4) (lane c1ParP 9) (lane c1LabP 9) 4 280 = true := by
  decide +kernel

theorem c1_pl : (c1.par.size == 280 && c1.lab.size == 280 && lane c1ParP 9 0 == 0 &&
    lane c1LabP 9 0 == 0) = true := by decide +kernel

theorem c1_pin : certPin c1 280 9 4 c1PtsP c1EdgesP c1ParP c1LabP = true := by decide +kernel

theorem rep1_ok : repLitQ orbLit nTabsP 1 w1 rp1P c1PtsP c1EdgesP c1ParP c1LabP c1.pts.toList =
    true := by decide +kernel

theorem w15_lit : (pathWord orbLit 280 15 == w15) = true := by decide +kernel

theorem rp15_pin : pin1 9 rp15.toList rp15P = true := by decide +kernel

theorem rp15_lit : (permL (tabR orbEdgesP) 280 w15 == rp15.toList) = true := by decide +kernel

theorem c15_replay : replayTOK (rdT c15EdgesP 9 4) (lane c15ParP 9) (lane c15LabP 9) 4 280 = true := by
  decide +kernel

theorem c15_pl : (c15.par.size == 280 && c15.lab.size == 280 && lane c15ParP 9 0 == 0 &&
    lane c15LabP 9 0 == 0) = true := by decide +kernel

theorem c15_pin : certPin c15 280 9 4 c15PtsP c15EdgesP c15ParP c15LabP = true := by
  decide +kernel

theorem rep15_ok : repLitQ orbLit nTabsP 15 w15 rp15P c15PtsP c15EdgesP c15ParP c15LabP
    c15.pts.toList = true := by decide +kernel

theorem w18_lit : (pathWord orbLit 280 18 == w18) = true := by decide +kernel

theorem rp18_pin : pin1 9 rp18.toList rp18P = true := by decide +kernel

theorem rp18_lit : (permL (tabR orbEdgesP) 280 w18 == rp18.toList) = true := by decide +kernel

theorem c18_replay : replayTOK (rdT c18EdgesP 9 4) (lane c18ParP 9) (lane c18LabP 9) 4 280 = true := by
  decide +kernel

theorem c18_pl : (c18.par.size == 280 && c18.lab.size == 280 && lane c18ParP 9 0 == 0 &&
    lane c18LabP 9 0 == 0) = true := by decide +kernel

theorem c18_pin : certPin c18 280 9 4 c18PtsP c18EdgesP c18ParP c18LabP = true := by
  decide +kernel

theorem rep18_ok : repLitQ orbLit nTabsP 18 w18 rp18P c18PtsP c18EdgesP c18ParP c18LabP
    c18.pts.toList = true := by decide +kernel

end CertificateChecks.J2Max76
