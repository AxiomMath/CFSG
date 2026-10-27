module

public import Certificates.Data.Kernel.EaLatF2
public import Certificates.Data.Kernel.Misc.PermClos
public import Certificates.Data.Kernel.Misc.G24
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_ktree CertificateChecks.KernelEaLat10506 V
  "Certificates/Kernel/EaLat10506/data/v.bin" 16 4 3056 6263951478994134643
#kc_repo #kc_ktree CertificateChecks.KernelEaLat10506 CM
  "Certificates/Kernel/EaLat10506/data/cm.bin" 32 4 6112 15228109552590153777
#kc_repo #kc_ktree CertificateChecks.KernelEaLat10506 PR
  "Certificates/Kernel/EaLat10506/data/pr.bin" 192 4 36672 9952522172554874477
#kc_repo #kc_ktree CertificateChecks.KernelEaLat10506 REC
  "Certificates/Kernel/EaLat10506/data/rec.bin" 136 4 1020952 418159326559965828
#kc_repo #kc_ktree CertificateChecks.KernelEaLat10506 CH
  "Certificates/Kernel/EaLat10506/data/ch.bin" 384 4 2882688 8489902287852714067
#kc_repo #kc_ktree CertificateChecks.KernelEaLat10506 PA
  "Certificates/Kernel/EaLat10506/data/pa.bin" 4 4 4096 17806345056043501844
#kc_repo #kc_ktree CertificateChecks.KernelEaLat10506 EC
  "Certificates/Kernel/EaLat10506/data/ec.bin" 16 4 16384 1285013633814251848
#kc_repo #kc_ktree CertificateChecks.KernelEaLat10506 TG
  "Certificates/Kernel/EaLat10506/data/tg.bin" 1 4 1024 7723833393169173603
#kc_repo #kc_ktree CertificateChecks.KernelEaLat10506 SG
  "Certificates/Kernel/EaLat10506/data/sg.bin" 2 4 2048 2927055161983844743
#kc_repo #kc_ktree CertificateChecks.KernelEaLat10506 CT
  "Certificates/Kernel/EaLat10506/data/ct.bin" 2 4 8192 10510783491044873143
#kc_repo #kc_ktree CertificateChecks.KernelEaLat10506 FX
  "Certificates/Kernel/EaLat10506/data/fx.bin" 256 4 48896 509272428224746638
#kc_repo #kc_ktree CertificateChecks.KernelEaLat10506 FV
  "Certificates/Kernel/EaLat10506/data/fv.bin" 256 4 1921792 12699883108590593053

public section

namespace CertificateChecks.KernelEaLat10506

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.EaLat

@[expose] noncomputable def M10 (x y : Nat) : Nat := CFSG.KC.Misc.G24.mulF2 (nat_lit 11) y x

@[expose] noncomputable def one10 : Nat := CFSG.KC.Misc.G24.oneF2 (nat_lit 11)

@[expose] noncomputable def GT (j : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat) 1300247336998927614937909652668524023
        1013442830293721029264202442113363238 (Nat.beq j (nat_lit 2)))
      1174917791885091810066549808485567970 (Nat.beq j (nat_lit 1)))
    1140926416586103782927740417499708916 (Nat.beq j (nat_lit 0))

@[expose] noncomputable def tagAt (o e : Nat) : Bool :=
  letB (TG e) fun t => letB (EC e) fun x =>
    Bool.rec (motive := fun _ => Bool)
      (orB (Nat.beq x o) (notB (Nat.beq (M10 x x) o)))
      (Nat.beq x (V t)) (Nat.blt t (nat_lit 191))

@[expose] noncomputable def ch10506e (k : Nat) : Bool :=
  letB one10 fun o =>
  allN (nat_lit 128) fun d => letB (Nat.add (Nat.mul (nat_lit 128) k) d) fun e =>
    andB (CFSG.KC.Misc.Clos.treeAt M10 o GT (nat_lit 4) EC PA e)
      (andB (CFSG.KC.Misc.Clos.sortAt (nat_lit 1024) EC SG e)
        (andB (CFSG.KC.Misc.Clos.closedAt M10 GT (nat_lit 4) (nat_lit 1024) EC CT e)
          (tagAt o e)))

@[expose] noncomputable def ncw11 (a b r : Nat) : Bool :=
  notB (Nat.beq (fld (M10 a b) (Nat.mul (nat_lit 11) r) (nat_lit 2047))
    (fld (M10 b a) (Nat.mul (nat_lit 11) r) (nat_lit 2047)))

@[expose] noncomputable def ch10506u (k : Nat) : Bool :=
  letB one10 fun o =>
  allN (nat_lit 16) fun d => letB (Nat.add (Nat.mul (nat_lit 16) k) d) fun i =>
    impB (Nat.blt i (nat_lit 191))
      (andB (uniAt M10 o (nat_lit 191) V CM PR ncw11 i) (fxAt FX V i))

@[expose] noncomputable def ch10506g (k : Nat) : Bool :=
  allN (nat_lit 278) fun d => letB (Nat.add (Nat.add (nat_lit 1) (Nat.mul (nat_lit 278) k)) d) fun f =>
    andB (genAt (nat_lit 191) REC CM PR f) (andB (covAt (nat_lit 7507) REC CH f) (fvAt FV FX REC f))

@[expose] noncomputable def ch10506z : Bool :=
  andB (baseOK (nat_lit 191) REC)
    (andB (covAt (nat_lit 7507) REC CH (nat_lit 0)) (fvAt FV FX REC (nat_lit 0)))

end CertificateChecks.KernelEaLat10506

end
