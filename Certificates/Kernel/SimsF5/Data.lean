module

public import Certificates.Data.Kernel.SimsF5.Defs
public import Certificates.Data.Kernel.CosetLat.Defs
public import Certificates.Data.Kernel.Misc.PermClos
import CFSG.Certificates.Kernel.Common.HarnessGzTree
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_ktree_gz CertificateChecks.KernelSimsF5 EL
  "Certificates/Kernel/SimsF5/data/el.bin.gz" 27 4 756 5461998891245028499
#kc_repo #kc_ktree_gz CertificateChecks.KernelSimsF5 TE
  "Certificates/Kernel/SimsF5/data/te.bin.gz" 27 4 3456 15754539143771265284
#kc_repo #kc_ktree_gz CertificateChecks.KernelSimsF5 TP
  "Certificates/Kernel/SimsF5/data/tp.bin.gz" 4 4 512 16515373528767269824
#kc_repo #kc_ktree_gz CertificateChecks.KernelSimsF5 TS
  "Certificates/Kernel/SimsF5/data/ts.bin.gz" 4 4 512 14795347859664200904
#kc_repo #kc_ktree_gz CertificateChecks.KernelSimsF5 TC
  "Certificates/Kernel/SimsF5/data/tc.bin.gz" 4 4 3584 14601873986252540200
#kc_repo #kc_ktree_gz CertificateChecks.KernelSimsF5 UE
  "Certificates/Kernel/SimsF5/data/ue.bin.gz" 27 4 10935 7686754580898558560
#kc_repo #kc_ktree_gz CertificateChecks.KernelSimsF5 UR
  "Certificates/Kernel/SimsF5/data/ur.bin.gz" 4 4 1620 13100182974232661115
#kc_repo #kc_ktree_gz CertificateChecks.KernelSimsF5 CR
  "Certificates/Kernel/SimsF5/data/cr.bin.gz" 8 4 27840 3411920031142834457
#kc_repo #kc_ktree_gz CertificateChecks.KernelSimsF5 MJ
  "Certificates/Kernel/SimsF5/data/mj.bin.gz" 4 4 120 12672152233972531851
#kc_repo #kc_ktree_gz CertificateChecks.KernelSimsF5 SE
  "Certificates/Kernel/SimsF5/data/se.bin.gz" 27 4 2808 6842432780095940297
#kc_repo #kc_ktree_gz CertificateChecks.KernelSimsF5 SP
  "Certificates/Kernel/SimsF5/data/sp.bin.gz" 4 4 416 1556692485785290591
#kc_repo #kc_ktree_gz CertificateChecks.KernelSimsF5 SS
  "Certificates/Kernel/SimsF5/data/ss.bin.gz" 4 4 416 14261729517050746571
#kc_repo #kc_ktree_gz CertificateChecks.KernelSimsF5 SC
  "Certificates/Kernel/SimsF5/data/sc.bin.gz" 4 4 1424 15450023617486633423
#kc_repo #kc_ktree_gz CertificateChecks.KernelSimsF5 SK
  "Certificates/Kernel/SimsF5/data/sk.bin.gz" 27 4 270 18402132722208739806
#kc_repo #kc_json_gz CertificateChecks.KernelSimsF5
  "Certificates/Kernel/SimsF5/data/w7600.json.gz" 1959 7731903421891008872
  (subW : List (List Nat)) (repW : List (List (List Nat))) (joinW : List (List (List Nat)))
  (incW : List (List (List Nat)))

public section

namespace CertificateChecks.KernelSimsF5

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.Clos CFSG.KC.CosetLat CFSG.KC.SimsF5

@[expose] noncomputable def lenL (t : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (nat_lit 8) (nat_lit 7) (Nat.beq t (nat_lit 0))

@[expose] noncomputable def LG (t j : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (EL (Nat.add (nat_lit 6) t)) (EL j) (Nat.blt j (nat_lit 7))

@[expose] noncomputable def LGG (a b l : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (LG b (Nat.sub l (lenL a))) (LG a l) (Nat.blt l (lenL a))

@[expose] noncomputable def RC (a : Nat) : Nat := EL (Nat.add (nat_lit 12) a)

@[expose] noncomputable def TR (j l : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (RC j) (EL l) (Nat.blt l (nat_lit 7))

@[expose] noncomputable def getW (l : List (List Nat)) (i : Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun x _ ih i => Bool.rec (motive := fun _ => List Nat) (ih (Nat.sub i 1)) x
      (Nat.beq i (nat_lit 0))) l i

@[expose] noncomputable def hd (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun x _ _ => x) l

@[expose] noncomputable def nth (l : List Nat) (i : Nat) : Nat := hd (List.drop i l)

@[expose] noncomputable def allIx (l : List (List (List Nat)))
    (f : Nat → List (List Nat) → Bool) (i₀ : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun x _ ih i => andB (f i x) (ih (Nat.succ i))) l i₀

@[expose] noncomputable def tOK : Bool :=
  allN (nat_lit 128) fun k => andB (treeAt m6 l6ONE EL (nat_lit 7) TE TP k)
    (andB (sortAt (nat_lit 128) TE TS k) (closedAt m6 EL (nat_lit 7) (nat_lit 128) TE TC k))

@[expose] noncomputable def uOK : Bool :=
  andB (Nat.beq (UE (nat_lit 0)) l6ONE)
    (allN (nat_lit 405) (transAt m6 RC (nat_lit 16) TE (nat_lit 128) UE UR))

@[expose] noncomputable def ch7600m0 (s : Nat) : Bool :=
  allR (Nat.mul (nat_lit 81) s) (nat_lit 81)
    (ctabAt m6 (LG (nat_lit 5)) (nat_lit 8) TE (nat_lit 128) UE (nat_lit 405) CR)

@[expose] noncomputable def memOK (t n o : Nat) : Bool :=
  andB (Nat.beq (MJ o) (nat_lit 0)) (andB (allN n fun i => Nat.blt (MJ (Nat.add o i)) (nat_lit 405))
    (allN n (ctabAt m6 (LG t) (nat_lit 8) TE (nat_lit 128) (fun i => UE (MJ (Nat.add o i))) n
      (fun r => CR (Nat.add (Nat.add (nat_lit 3240) (Nat.mul (nat_lit 8) o)) r)))))

@[expose] noncomputable def subOK (t N nK oE oC oK : Nat) : Bool :=
  andB (allN nK fun j => wordAt m6 l6ONE (LG t) (lenL t) (getW subW (Nat.add oK j))
      (SK (Nat.add oK j)))
    (allN N fun k => andB
      (treeAt m6 l6ONE (fun j => SK (Nat.add oK j)) nK (fun i => SE (Nat.add oE i))
        (fun i => SP (Nat.add oE i)) k)
      (andB (sortAt N (fun i => SE (Nat.add oE i)) (fun i => SS (Nat.add oE i)) k)
        (closedAt m6 (fun j => SK (Nat.add oK j)) nK N (fun i => SE (Nat.add oE i))
          (fun r => SC (Nat.add oC r)) k)))

@[expose] noncomputable def repAt (j : Nat) (e : List (List Nat)) : Bool :=
  letB (hd (getW e 0)) fun t => andB (Nat.blt t (nat_lit 6))
    (andB (impB (notB (Nat.beq t (nat_lit 0)))
        (wordAt m6 l6ONE (TR j) (nat_lit 8) (getW e 1) (EL (Nat.add (nat_lit 6) t))))
      (wordAt m6 l6ONE (LG t) (lenL t) (getW e 2) (RC j)))

@[expose] noncomputable def repOK : Bool :=
  andB (Nat.beq (List.length repW) (nat_lit 16)) (allIx repW repAt (nat_lit 0))

@[expose] noncomputable def joinAt (e : List (List Nat)) : Bool :=
  letB (nth (getW e 0) 0) fun a => letB (nth (getW e 0) 1) fun b =>
  letB (nth (getW e 0) 2) fun c =>
    andB (Nat.blt a (nat_lit 6)) (andB (Nat.blt b (nat_lit 6)) (andB (Nat.blt c (nat_lit 6))
    (andB (impB (notB (Nat.beq c (nat_lit 0)))
      (wordAt m6 l6ONE (LGG a b) (Nat.add (lenL a) (lenL b)) (getW e 1)
        (EL (Nat.add (nat_lit 6) c))))
    (andB (impB (notB (Nat.beq a (nat_lit 0)))
      (wordAt m6 l6ONE (LG c) (lenL c) (getW e 2) (EL (Nat.add (nat_lit 6) a))))
    (impB (notB (Nat.beq b (nat_lit 0)))
      (wordAt m6 l6ONE (LG c) (lenL c) (getW e 3) (EL (Nat.add (nat_lit 6) b))))))))

@[expose] noncomputable def joinOK : Bool :=
  andB (allIx joinW (fun _ e => joinAt e) (nat_lit 0))
    (allN (nat_lit 6) fun a => allN (nat_lit 6) fun b =>
      notB (allIx joinW (fun _ e => notB (andB (Nat.beq (nth (getW e 0) 0) a)
        (Nat.beq (nth (getW e 0) 1) b))) (nat_lit 0)))

@[expose] noncomputable def incOK : Bool :=
  allIx incW (fun _ e => wordAt m6 l6ONE (LG (nth (getW e 0) 1)) (lenL (nth (getW e 0) 1))
    (getW e 1) (EL (Nat.add (nat_lit 6) (nth (getW e 0) 0)))) (nat_lit 0)

@[expose] noncomputable def notOK : Bool :=
  allN (nat_lit 3) (notInAt m6 TE (nat_lit 128) (fun i => UE (MJ (Nat.add (nat_lit 3) i)))
    (EL (nat_lit 7)))

end CertificateChecks.KernelSimsF5

end
