module

public import Certificates.Kernel.LyBase.Data
public import Certificates.Kernel.LyBenes.Words

public section

namespace CertificateChecks.KernelLyBase

open CFSG.KC.LyBase CertificateChecks.KernelLy CertificateChecks.KernelLyB
  CFSG.Sporadic.Recognition.LyonsSims.LyFinal

@[expose] noncomputable def famFix (j : Nat) : Bool :=
  (((Rcore107 ++ modularLearned).drop (16 * j)).take 16).all fun r => !isBWord r || wB r

@[expose] noncomputable def stepFix (s : Dist2Step) : Bool :=
  match s.kind with
  | .B => wB (parseWord s.old ++ derivInv (parseWord s.new))
  | _ => true

@[expose] noncomputable def stepFixChunk (i j : Nat) : Bool :=
  (((stepsAt i).drop (40 * j)).take 40).all stepFix

@[expose] noncomputable def invFix : Bool :=
  ([(0 : Fin 6), 2, 3, 4].map fun i => [(i, true), (i, true)]).all wB

@[expose] noncomputable def s1Fix : Bool := S1.all (fixAll cL dL [0])

@[expose] noncomputable def s2Fix : Bool := S2.all (fixAll cL dL [0, 3])

@[expose] noncomputable def orb0 : Bool := orbitOK W0 R0 0 66825

@[expose] noncomputable def orb1 : Bool := orbitOK W1 R1 3 20160

@[expose] noncomputable def tree2 : Bool := treeOK cL dL S2 1 4 O2 T2

end CertificateChecks.KernelLyBase

end
