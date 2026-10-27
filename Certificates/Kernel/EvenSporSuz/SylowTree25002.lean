module

public import Certificates.Data.Kernel.EvenSporSuz.SylowTree
public import Certificates.Kernel.EvenSporSuz.SylowData25002
public import Certificates.Kernel.EvenSporSuz.SylowTreeData25002
public import CFSG.Certificates.Kernel.Common.EachTrue
import all Init.Data.List.SplitOn.Basic

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSyl25002

open CFSG.KC.EvenSporSuz.Syl CFSG.KC.ONanSmall CFSG.KC.Misc.G24

@[expose] noncomputable def QT : KTree (Nat × Nat) := treeOf (idxL id ps 0)

@[expose] noncomputable def ET : KTree (Nat × Nat) := treeOf (idxL Prod.fst ed 0)

set_option maxHeartbeats 0 in
theorem treeGlob_true : (bindTP tp tokT && Nat.beq tp.length 16383 && Nat.beq ps.length 16384 &&
    Nat.beq iv.length 16384) = true := by decide +kernel

#kc_each CertificateChecks.KernelSyl25002 tr25002 (fun i => treeChunkK QT ET gs ps tp iv i) 0 4

set_option maxHeartbeats 0 in
theorem treeElem_bad : (!elemT QT ET gs 1 (ps.getD 2 0) (0, 0)) = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem treePos_bad : (!posGo QT [iv.getD 1 0] 0) = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem treeBind_bad : (!bindTP (tp.drop 1) tokT) = true := by decide +kernel

end CertificateChecks.KernelSyl25002
