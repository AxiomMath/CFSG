module

public import Certificates.Kernel.L52Insp443.Data
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelL52I

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.GLM CFSG.KC.L52I

@[expose] noncomputable def ch725109z (z : Nat) : Bool :=
  andB (listBeq (spanK (D.zB.getD z [])) (D.zS.getD z [])) (andB (nodupK (D.zS.getD z []))
    (andB (allK (fun s => allK (commK s) (D.zB.getD z [])) (D.zS.getD z []))
      (Nat.beq (solCntK (diagK (D.zB.getD z []))) (nat_lit 16))))

@[expose] noncomputable def ch725109w (w : Nat) : Bool :=
  andB (listBeq (spanK (List.append (D.a0B.getD w []) (D.a1B.getD w []))) (D.wS.getD w []))
    (andB (nodupK (D.wS.getD w []))
    (andB (listBeq ((D.aB.getD w []).getD 0 []) (D.a0B.getD w []))
    (andB (listBeq ((D.aB.getD w []).getD 1 []) (D.a1B.getD w []))
    (andB (listBeq ((D.aB.getD w []).getD 2 [])
      (List.zipWith mmulK (D.a0B.getD w []) (D.a1B.getD w [])))
    (andB (Nat.beq (List.length (D.aB.getD w [])) (nat_lit 3))
    (andB (Nat.beq (List.length (D.aS.getD w [])) (nat_lit 3))
    (andB (allK (fun i => listBeq (spanK ((D.aB.getD w []).getD i [])) ((D.aS.getD w []).getD i []))
      (List.range 3))
    (andB (allK (fun s => allK (commK s) (D.a0B.getD w [])) (D.wS.getD w []))
    (andB (Nat.beq (solCntK (diagK (D.a0B.getD w []))) (nat_lit 128))
      (tauOK (D.a0B.getD w []) (D.a1B.getD w []) (D.wS.getD w []) ((D.aS.getD w []).getD 1 [])
        (D.tau.getD w 0)))))))))))

@[expose] noncomputable def ch725109k (k : Nat) : Bool :=
  andB (allK (fun s => allK (commK s) (D.k1B.getD k [])) (D.wS.getD (D.k1zw.getD k (0, 0)).2 []))
    (andB (allK (fun s => allK (commK s) (D.k1B.getD k [])) (D.zS.getD (D.k1zw.getD k (0, 0)).1 []))
    (andB (Nat.beq (solCntK (diagK (D.k1B.getD k []))) (nat_lit 128))
      (listBeq (kerK (diagK (D.k1B.getD k []))) (D.k1K.getD k []))))

@[expose] noncomputable def ch725109c (k : Nat) : Bool :=
  andB (allK (fun s => allK (commK s) (D.k2B.getD k [])) (D.wS.getD (D.k2w.getD k 0) []))
    (Nat.beq (solCntK (diagK (D.k2B.getD k []))) (nat_lit 64))

@[expose] noncomputable def ch725109x (_ : Nat) : Bool :=
  andB (Nat.beq (D.x7p.getD 0 0) idK)
    (andB (allK (fun j => Nat.beq (mmulK (D.x7p.getD j 0) (D.x7p.getD 1 0)) (D.x7p.getD (j + 1) 0))
      (List.range 6))
    (andB (Nat.beq (List.length D.x7p) (nat_lit 7)) (andB (Nat.beq (List.length D.x7q) (nat_lit 7))
    (andB (allK (fun j => Nat.beq (mmulK (D.x7p.getD j 0) (D.x7q.getD j 0)) idK) (List.range 7))
    (andB (ordK (D.x7p.getD 1 0) (nat_lit 7))
      (allK (fun i => Nat.beq (mmulK (D.gs.getD i 0) (D.gis.getD i 0)) idK) (List.range 2)))))))

#kc_each ch725109z 0 7
#kc_each ch725109w 0 2
#kc_each ch725109k 0 6
#kc_each ch725109c 0 12
#kc_each ch725109x 0 1

end CertificateChecks.KernelL52I

end
