module

public import Certificates.Data.Kernel.EaLat
public import Certificates.Data.Kernel.Misc.PermClos
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_ktree CertificateChecks.KernelEaLat318002 V
  "Certificates/Kernel/EaLat318002/data/v.bin" 16 4 3056 2226663088835955194
#kc_repo #kc_ktree CertificateChecks.KernelEaLat318002 CM
  "Certificates/Kernel/EaLat318002/data/cm.bin" 32 4 6112 4508443934867214732
#kc_repo #kc_ktree CertificateChecks.KernelEaLat318002 PR
  "Certificates/Kernel/EaLat318002/data/pr.bin" 192 4 36672 7118164802005156891
#kc_repo #kc_ktree CertificateChecks.KernelEaLat318002 REC
  "Certificates/Kernel/EaLat318002/data/rec.bin" 136 4 1020952 14666997039820091673
#kc_repo #kc_ktree CertificateChecks.KernelEaLat318002 CH
  "Certificates/Kernel/EaLat318002/data/ch.bin" 384 4 2882688 5021225435967828311
#kc_repo #kc_ktree CertificateChecks.KernelEaLat318002 PA
  "Certificates/Kernel/EaLat318002/data/pa.bin" 4 4 4096 13426254628595662067
#kc_repo #kc_ktree CertificateChecks.KernelEaLat318002 EC
  "Certificates/Kernel/EaLat318002/data/ec.bin" 16 4 16384 13085632137409478979
#kc_repo #kc_ktree CertificateChecks.KernelEaLat318002 TG
  "Certificates/Kernel/EaLat318002/data/tg.bin" 1 4 1024 14679756327253555675
#kc_repo #kc_ktree CertificateChecks.KernelEaLat318002 SG
  "Certificates/Kernel/EaLat318002/data/sg.bin" 2 4 2048 4401044407384454821
#kc_repo #kc_ktree CertificateChecks.KernelEaLat318002 CT
  "Certificates/Kernel/EaLat318002/data/ct.bin" 2 4 8192 12081209751459315882

public section

namespace CertificateChecks.KernelEaLat318002

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.EaLat

@[expose] noncomputable def GR (j : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat) 354539360347563751963318968304164522
        357057498396763603582949468095501504 (Nat.beq j (nat_lit 2)))
      897242705448095582492724874614902816 (Nat.beq j (nat_lit 1)))
    901804871909372407349126060950521888 (Nat.beq j (nat_lit 0))

@[expose] noncomputable def tagAt (o e : Nat) : Bool :=
  letB (TG e) fun t => letB (EC e) fun x =>
    Bool.rec (motive := fun _ => Bool)
      (orB (Nat.beq x o) (notB (Nat.beq (mul (nat_lit 24) x x) o)))
      (Nat.beq x (V t)) (Nat.blt t (nat_lit 191))

@[expose] noncomputable def ch318002e (k : Nat) : Bool :=
  letB (one (nat_lit 24)) fun o =>
  allN (nat_lit 128) fun d => letB (Nat.add (Nat.mul (nat_lit 128) k) d) fun e =>
    andB (CFSG.KC.Misc.Clos.treeAt (mul (nat_lit 24)) o GR (nat_lit 4) EC PA e)
      (andB (CFSG.KC.Misc.Clos.sortAt (nat_lit 1024) EC SG e)
        (andB (CFSG.KC.Misc.Clos.closedAt (mul (nat_lit 24)) GR (nat_lit 4) (nat_lit 1024) EC CT e)
          (tagAt o e)))

@[expose] noncomputable def ncw24 (a b w : Nat) : Bool :=
  notB (Nat.beq (img a (img b w)) (img b (img a w)))

@[expose] noncomputable def ch318002u (k : Nat) : Bool :=
  allN (nat_lit 16) fun d => letB (Nat.add (Nat.mul (nat_lit 16) k) d) fun i =>
    impB (Nat.blt i (nat_lit 191))
      (uniAt (mul (nat_lit 24)) (one (nat_lit 24)) (nat_lit 191) V CM PR ncw24 i)

@[expose] noncomputable def ch318002g (k : Nat) : Bool :=
  allN (nat_lit 278) fun d => letB (Nat.add (Nat.add (nat_lit 1) (Nat.mul (nat_lit 278) k)) d) fun f =>
    andB (genAt (nat_lit 191) REC CM PR f) (covAt (nat_lit 7507) REC CH f)

@[expose] noncomputable def ch318002z : Bool :=
  andB (baseOK (nat_lit 191) REC) (covAt (nat_lit 7507) REC CH (nat_lit 0))

end CertificateChecks.KernelEaLat318002

end
