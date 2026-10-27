module

public import Certificates.Data.Kernel.EvenSporSuz.F2
public import Certificates.Kernel.EvenSporSuz.F2Data1379102
public import Certificates.Kernel.EvenSporSuz.SylowBind25002
import all Init.Data.List.SplitOn.Basic

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelF21379102

open CFSG.KC.EvenSporSuz CFSG.KC.EvenSporSuz.Syl CFSG.KC.EvenSporSuz.F2 CFSG.KC.Misc.G24
  CertificateChecks.KernelSuz CertificateChecks.KernelSyl25002

@[expose] noncomputable def T3 : CFSG.KC.ONanSmall.KTree (Nat × Nat) := treeOf els

@[expose] noncomputable def TQ : CFSG.KC.ONanSmall.KTree (Nat × Nat) := treeOf qels

set_option maxHeartbeats 0 in
theorem inv_true : (invK gs gi 4 && invK ab abi 5 && invK n2 n2i 7 && invK n3 n3i 6 &&
    invK qL qL 3 && invK ys yis 6) = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ab_true : allBelow 5 (fun t => Nat.beq (ab.getD t 0) (abL.getD t 0)) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ys_true : allBelow 4 (fun t => Nat.beq (ys.getD t 0) (gs.getD t 0)) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem n2_true : comK gs gi gs gi g2u g2v n2 7 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem n3_true : comK n2 n2i gs gi m2u g3v n3 6 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem m2c_true : memK n2 n2i m2c (fun t => mulF3 (mulF3 (gs.getD (t / 7) 0) (n2.getD (t % 7) 0))
    (gi.getD (t / 7) 0)) 28 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem m2a_true : memK n2 n2i m2a (fun t => mulF3 (mulF3 (mulF3 (gs.getD (t / 4) 0)
    (gs.getD (t % 4) 0)) (gi.getD (t / 4) 0)) (gi.getD (t % 4) 0)) 16 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem m3c_true : memK n3 n3i m3c (fun t => mulF3 (mulF3 (gs.getD (t / 6) 0) (n3.getD (t % 6) 0))
    (gi.getD (t / 6) 0)) 24 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem m3a_true : memK n3 n3i m3a (fun t => mulF3 (mulF3 (mulF3 (n2.getD (t / 4) 0)
    (gs.getD (t % 4) 0)) (n2i.getD (t / 4) 0)) (gi.getD (t % 4) 0)) 28 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem enum3_true : enumK T3 n3 n3i 6 128 els = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem cen3_true : cenK n3 6 els 32 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem q_true : memK gs gi q (fun t => qL.getD t 0) 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem enumQ_true : enumK TQ qL qL 3 8 qels = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem cenQ_true : cenK qL 3 qels 8 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem c_true : (memK ab abi [c1, c2] (fun t => ys.getD (4 + t) 0) 2 &&
    cenB qL 3 (ys.getD 4 0) && cenB qL 3 (ys.getD 5 0)) = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem wy_true : memK ys yis wy (fun t => lanesL (cgL t)) 7 = true := by decide +kernel

end CertificateChecks.KernelF21379102
