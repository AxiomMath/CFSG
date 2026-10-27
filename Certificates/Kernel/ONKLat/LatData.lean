module

public import Certificates.Data.Kernel.CosetLat.Defs
public import Certificates.Data.Kernel.Misc.PermClos
public import Certificates.Data.Kernel.Spor.Chain
import CFSG.Certificates.Kernel.Common.HarnessGzTree
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_ktree_gz CertificateChecks.KernelONKLat EL
  "Certificates/Kernel/ONKLat/data/el.bin.gz" 105 4 1995 13503387921255215058
#kc_repo #kc_ktree_gz CertificateChecks.KernelONKLat TE
  "Certificates/Kernel/ONKLat/data/te.bin.gz" 105 4 13440 13201770863331068737
#kc_repo #kc_ktree_gz CertificateChecks.KernelONKLat TP
  "Certificates/Kernel/ONKLat/data/tp.bin.gz" 4 4 512 16759274585063113815
#kc_repo #kc_ktree_gz CertificateChecks.KernelONKLat TS
  "Certificates/Kernel/ONKLat/data/ts.bin.gz" 4 4 512 17505766093811879063
#kc_repo #kc_ktree_gz CertificateChecks.KernelONKLat TC
  "Certificates/Kernel/ONKLat/data/tc.bin.gz" 4 4 1536 3762301704764579858
#kc_repo #kc_ktree_gz CertificateChecks.KernelONKLat UE
  "Certificates/Kernel/ONKLat/data/ue.bin.gz" 105 4 33075 5685902131541005915
#kc_repo #kc_ktree_gz CertificateChecks.KernelONKLat UR
  "Certificates/Kernel/ONKLat/data/ur.bin.gz" 4 4 1260 13218512004346405204
#kc_repo #kc_ktree_gz CertificateChecks.KernelONKLat CR
  "Certificates/Kernel/ONKLat/data/cr.bin.gz" 8 4 5040 14709025149440047696
#kc_repo #kc_json_gz CertificateChecks.KernelONKLat
  "Certificates/Kernel/ONKLat/data/w812105.json.gz" 1831 5287312557862080550
  (repM : List (List Nat)) (repW : List (List (List Nat))) (joinW : List (List (List Nat)))
  (h3W : List Nat)

public section

namespace CertificateChecks.KernelONKLat

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.Clos CFSG.KC.CosetLat

@[expose] noncomputable def m120 : Nat → Nat → Nat :=
  CFSG.KC.Enum.pcomp (nat_lit 120) (nat_lit 7) (CFSG.KS.mask (nat_lit 7))

@[expose] noncomputable def one120 : Nat := CFSG.KC.Enum.pidn (nat_lit 120) (nat_lit 7)

@[expose] noncomputable def lenL (t : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (nat_lit 3) (nat_lit 2) (Nat.beq t (nat_lit 2))

@[expose] noncomputable def LG (t j : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat) (EL (Nat.add (nat_lit 3) j)) (EL (Nat.add (nat_lit 5) j))
      (Nat.beq t (nat_lit 1)))
    (EL j) (Nat.beq t (nat_lit 0))

@[expose] noncomputable def MG (j : Nat) : Nat := EL (Nat.add (nat_lit 3) j)

@[expose] noncomputable def LGG (a b l : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (LG b (Nat.sub l (lenL a))) (LG a l) (Nat.blt l (lenL a))

@[expose] noncomputable def RC (a : Nat) : Nat := EL (Nat.add (nat_lit 8) a)

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

@[expose] noncomputable def wordsAt (A : Nat → Nat) (nA : Nat) (ws : List (List Nat)) (o : Nat)
    (G : Nat → Nat) (n : Nat) : Bool :=
  allN n fun k => wordAt m120 one120 A nA (getW ws (Nat.add o k)) (G k)

@[expose] noncomputable def tOK : Bool :=
  allN (nat_lit 128) fun k => andB (treeAt m120 one120 EL (nat_lit 3) TE TP k)
    (andB (sortAt (nat_lit 128) TE TS k) (closedAt m120 EL (nat_lit 3) (nat_lit 128) TE TC k))

@[expose] noncomputable def uOK : Bool :=
  andB (Nat.beq (UE (nat_lit 0)) one120)
    (allN (nat_lit 315) (transAt m120 RC (nat_lit 10) TE (nat_lit 128) UE UR))

@[expose] noncomputable def ch812105m (s : Nat) : Bool :=
  allR (Nat.mul (nat_lit 105) s) (nat_lit 105)
    (ctabAt m120 MG (nat_lit 2) TE (nat_lit 128) UE (nat_lit 315) CR)

@[expose] noncomputable def repMOK : Bool :=
  wordsAt MG (nat_lit 2) repM (nat_lit 0) RC (nat_lit 10)

@[expose] noncomputable def repAt (j : Nat) (e : List (List Nat)) : Bool :=
  letB (hd (getW e 0)) fun t => andB (Nat.blt t (nat_lit 3))
    (andB (wordAt m120 one120 (LG t) (lenL t) (getW e 1) (RC j))
      (wordsAt (TR j) (nat_lit 4) e (nat_lit 2) (LG t) (lenL t)))

@[expose] noncomputable def repOK : Bool :=
  andB (Nat.beq (List.length repW) (nat_lit 10)) (allIx repW repAt (nat_lit 0))

@[expose] noncomputable def joinAt (e : List (List Nat)) : Bool :=
  letB (nth (getW e 0) 0) fun a => letB (nth (getW e 0) 1) fun b =>
  letB (nth (getW e 0) 2) fun c =>
    andB (Nat.blt a (nat_lit 3)) (andB (Nat.blt b (nat_lit 3)) (andB (Nat.blt c (nat_lit 3))
    (andB (wordsAt (LGG a b) (Nat.add (lenL a) (lenL b)) e (nat_lit 1) (LG c) (lenL c))
    (andB (wordsAt (LG c) (lenL c) e (Nat.add (nat_lit 1) (lenL c)) (LG a) (lenL a))
      (wordsAt (LG c) (lenL c) e (Nat.add (Nat.add (nat_lit 1) (lenL c)) (lenL a)) (LG b)
        (lenL b))))))

@[expose] noncomputable def joinOK : Bool :=
  andB (allIx joinW (fun _ e => joinAt e) (nat_lit 0))
    (allN (nat_lit 3) fun a => allN (nat_lit 3) fun b =>
      notB (allIx joinW (fun _ e => notB (andB (Nat.beq (nth (getW e 0) 0) a)
        (Nat.beq (nth (getW e 0) 1) b))) (nat_lit 0)))

@[expose] noncomputable def h3OK : Bool :=
  andB (wordAt m120 one120 (LG (nat_lit 1)) (nat_lit 3) h3W (EL (nat_lit 18)))
    (andB (Nat.beq (m120 (EL (nat_lit 18)) (m120 (EL (nat_lit 18)) (EL (nat_lit 18)))) one120)
      (notB (Nat.beq (EL (nat_lit 18)) one120)))

end CertificateChecks.KernelONKLat

end
