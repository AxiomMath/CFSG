module

public import Certificates.Data.Kernel.CosetLat.Avoid
public import Certificates.Data.Kernel.Misc.PermClos
public import Certificates.Data.Kernel.Spor.Chain
import CFSG.Certificates.Kernel.Common.HarnessGzTree
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_ktree_gz CertificateChecks.KernelU42Lat EL
  "Certificates/Kernel/U42Lat/data/el.bin.gz" 34 4 1224 12433712086100545280
#kc_repo #kc_ktree_gz CertificateChecks.KernelU42Lat TE
  "Certificates/Kernel/U42Lat/data/te.bin.gz" 34 4 2176 17561405795144075433
#kc_repo #kc_ktree_gz CertificateChecks.KernelU42Lat TP
  "Certificates/Kernel/U42Lat/data/tp.bin.gz" 4 4 256 7430492118311566423
#kc_repo #kc_ktree_gz CertificateChecks.KernelU42Lat TS
  "Certificates/Kernel/U42Lat/data/ts.bin.gz" 4 4 256 13555701462154184577
#kc_repo #kc_ktree_gz CertificateChecks.KernelU42Lat TC
  "Certificates/Kernel/U42Lat/data/tc.bin.gz" 4 4 768 13606741015103419677
#kc_repo #kc_ktree_gz CertificateChecks.KernelU42Lat UE
  "Certificates/Kernel/U42Lat/data/ue.bin.gz" 34 4 13770 15773376770897291535
#kc_repo #kc_ktree_gz CertificateChecks.KernelU42Lat UR
  "Certificates/Kernel/U42Lat/data/ur.bin.gz" 4 4 1620 14291298003787082242
#kc_repo #kc_ktree_gz CertificateChecks.KernelU42Lat CR
  "Certificates/Kernel/U42Lat/data/cr.bin.gz" 8 4 7440 12690703646209561464
#kc_repo #kc_ktree_gz CertificateChecks.KernelU42Lat MJ
  "Certificates/Kernel/U42Lat/data/mj.bin.gz" 4 4 120 13708985409745502522
#kc_repo #kc_ktree_gz CertificateChecks.KernelU42Lat SE
  "Certificates/Kernel/U42Lat/data/se.bin.gz" 34 4 3706 13847872670433366156
#kc_repo #kc_ktree_gz CertificateChecks.KernelU42Lat SP
  "Certificates/Kernel/U42Lat/data/sp.bin.gz" 4 4 436 7478323554391881667
#kc_repo #kc_ktree_gz CertificateChecks.KernelU42Lat SS
  "Certificates/Kernel/U42Lat/data/ss.bin.gz" 4 4 436 641449908983416665
#kc_repo #kc_ktree_gz CertificateChecks.KernelU42Lat SC
  "Certificates/Kernel/U42Lat/data/sc.bin.gz" 4 4 1120 5931959303075627855
#kc_repo #kc_ktree_gz CertificateChecks.KernelU42Lat SK
  "Certificates/Kernel/U42Lat/data/sk.bin.gz" 34 4 340 8351228004739869943
#kc_repo #kc_json_gz CertificateChecks.KernelU42Lat
  "Certificates/Kernel/U42Lat/data/w409001.json.gz" 2403 14702181852370238359
  (subW : List (List Nat)) (repW : List (List (List Nat))) (joinW : List (List (List Nat)))
  (incW : List (List Nat))

public section

namespace CertificateChecks.KernelU42Lat

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.Clos CFSG.KC.CosetLat

@[expose] noncomputable def mU (p q : Nat) : Nat :=
  CFSG.KC.Enum.pcomp (nat_lit 45) (nat_lit 6) (CFSG.KS.mask (nat_lit 6)) p q

@[expose] noncomputable def oneU : Nat := CFSG.KC.Enum.pidn (nat_lit 45) (nat_lit 6)

@[expose] noncomputable def lenF (t : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat) (nat_lit 4) (nat_lit 2) (Nat.beq t (nat_lit 6)))
    (nat_lit 3) (Nat.beq t (nat_lit 0))

@[expose] noncomputable def FG (t j : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat) (EL (Nat.add (nat_lit 2) t)) (EL j) (Nat.blt j (nat_lit 3)))
    (EL (Nat.add (nat_lit 8) j)) (Nat.beq t (nat_lit 6))

@[expose] noncomputable def FGG (a b l : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (FG b (Nat.sub l (lenF a))) (FG a l) (Nat.blt l (lenF a))

@[expose] noncomputable def RC (a : Nat) : Nat := EL (Nat.add (nat_lit 10) a)

@[expose] noncomputable def TR (j l : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (RC j) (EL l) (Nat.blt l (nat_lit 3))

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
  allN (nat_lit 64) fun k => andB (treeAt mU oneU EL (nat_lit 3) TE TP k)
    (andB (sortAt (nat_lit 64) TE TS k) (closedAt mU EL (nat_lit 3) (nat_lit 64) TE TC k))

@[expose] noncomputable def uOK : Bool :=
  andB (Nat.beq (UE (nat_lit 0)) oneU)
    (allN (nat_lit 405) (transAt mU RC (nat_lit 24) TE (nat_lit 64) UE UR))

@[expose] noncomputable def ch409001m (s : Nat) : Bool :=
  allR (Nat.mul (nat_lit 135) s) (nat_lit 135)
    (ctabAt mU (FG (nat_lit 6)) (nat_lit 2) TE (nat_lit 64) UE (nat_lit 405) CR)

@[expose] noncomputable def memOK (t n o : Nat) : Bool :=
  andB (Nat.beq (MJ o) (nat_lit 0)) (andB (allN n fun i => Nat.blt (MJ (Nat.add o i)) (nat_lit 405))
    (allN n (ctabAt mU (FG t) (nat_lit 4) TE (nat_lit 64) (fun i => UE (MJ (Nat.add o i))) n
      (fun r => CR (Nat.add (Nat.add (nat_lit 810) (Nat.mul (nat_lit 4) o)) r)))))

@[expose] noncomputable def subOK (t N nK oE oC oK : Nat) : Bool :=
  andB (allN nK fun j => wordAt mU oneU (FG t) (lenF t) (getW subW (Nat.add oK j))
      (SK (Nat.add oK j)))
    (allN N fun k => andB
      (treeAt mU oneU (fun j => SK (Nat.add oK j)) nK (fun i => SE (Nat.add oE i))
        (fun i => SP (Nat.add oE i)) k)
      (andB (sortAt N (fun i => SE (Nat.add oE i)) (fun i => SS (Nat.add oE i)) k)
        (closedAt mU (fun j => SK (Nat.add oK j)) nK N (fun i => SE (Nat.add oE i))
          (fun r => SC (Nat.add oC r)) k)))

@[expose] noncomputable def repAt (j : Nat) (e : List (List Nat)) : Bool :=
  letB (hd (getW e 0)) fun t => andB (Nat.blt t (nat_lit 6))
    (andB (impB (notB (Nat.beq t (nat_lit 0)))
        (wordAt mU oneU (TR j) (nat_lit 4) (getW e 1) (EL (Nat.add (nat_lit 2) t))))
      (wordAt mU oneU (FG t) (lenF t) (getW e 2) (RC j)))

@[expose] noncomputable def repOK : Bool :=
  andB (Nat.beq (List.length repW) (nat_lit 24)) (allIx repW repAt (nat_lit 0))

@[expose] noncomputable def joinAt (e : List (List Nat)) : Bool :=
  letB (nth (getW e 0) 0) fun a => letB (nth (getW e 0) 1) fun b =>
  letB (nth (getW e 0) 2) fun c =>
    andB (Nat.blt a (nat_lit 6)) (andB (Nat.blt b (nat_lit 6)) (andB (Nat.blt c (nat_lit 6))
    (andB (impB (notB (Nat.beq c (nat_lit 0)))
      (wordAt mU oneU (FGG a b) (Nat.add (lenF a) (lenF b)) (getW e 1)
        (EL (Nat.add (nat_lit 2) c))))
    (andB (impB (notB (Nat.beq a (nat_lit 0)))
      (wordAt mU oneU (FG c) (lenF c) (getW e 2) (EL (Nat.add (nat_lit 2) a))))
    (impB (notB (Nat.beq b (nat_lit 0)))
      (wordAt mU oneU (FG c) (lenF c) (getW e 3) (EL (Nat.add (nat_lit 2) b))))))))

@[expose] noncomputable def joinOK : Bool :=
  andB (allIx joinW (fun _ e => joinAt e) (nat_lit 0))
    (allN (nat_lit 6) fun a => allN (nat_lit 6) fun b =>
      notB (allIx joinW (fun _ e => notB (andB (Nat.beq (nth (getW e 0) 0) a)
        (Nat.beq (nth (getW e 0) 1) b))) (nat_lit 0)))

@[expose] noncomputable def incOK : Bool :=
  andB (allN (nat_lit 8) fun i =>
      wordAt mU oneU (FG (nat_lit 6)) (nat_lit 2) (getW incW i) (EL i))
    (allN (nat_lit 2) fun j => wordAt mU oneU (FG (nat_lit 5)) (nat_lit 4)
      (getW incW (Nat.add (nat_lit 8) j)) (EL (Nat.add (nat_lit 8) j)))

@[expose] noncomputable def d0OK : Bool :=
  andB (Nat.beq (SK (nat_lit 2)) (EL (nat_lit 34))) (andB (Nat.beq (SK (nat_lit 3)) (EL (nat_lit 35)))
    (andB (Nat.beq (mU (mU (EL (nat_lit 34)) (EL (nat_lit 34))) (EL (nat_lit 34))) oneU)
    (andB (Nat.beq (mU (mU (EL (nat_lit 35)) (EL (nat_lit 35))) (EL (nat_lit 35))) oneU)
      (allN (nat_lit 9) (allCosAt mU TE (nat_lit 64) (fun i => UE (MJ (Nat.add (nat_lit 6) i)))
        (invPairAt mU (EL (nat_lit 34)) (mU (EL (nat_lit 34)) (EL (nat_lit 34)))
          (EL (nat_lit 35)) (mU (EL (nat_lit 35)) (EL (nat_lit 35)))))))))

end CertificateChecks.KernelU42Lat

end
