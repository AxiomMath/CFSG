module

public import Certificates.Data.Kernel.EvenSporSuz.Sylow
public import Certificates.Kernel.EvenSporSuz.SylowData25002
public import CFSG.Certificates.Kernel.Common.EachTrue

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSyl25002

open CFSG.KC.EvenSporSuz.Syl CFSG.KC.ONanSmall CFSG.KC.Misc.G24

@[expose] noncomputable def T : KTree (Nat × Nat) := treeOf ed

@[expose] noncomputable def OT : KTree (Nat × Nat) := treeOf od

set_option maxHeartbeats 0 in
theorem glob_true : globK gs gi z x1 x2 r c tg ed sz s1 s2 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem orb_true : od.all (fun p => orbK OT gs gi r p.1 p.2) = true := by decide +kernel

#kc_each CertificateChecks.KernelSyl25002 ch25002
  (fun i => chunkK T OT gs gi z x1 x2 ed sz s1 s2 i) 0 16

set_option maxHeartbeats 0 in
theorem elem_bad : (!elemK T OT gs gi z (one3 + 1) 0 one3) = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem orb_bad : (!orbK OT gs gi r z 4) = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem glob_bad : (!globK gs gi x1 x1 x2 r c tg ed sz s1 s2) = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem chunk_bad : (!chunkGo T OT gs gi z x1 x2 [] 1 0 0) = true := by decide +kernel

end CertificateChecks.KernelSyl25002
