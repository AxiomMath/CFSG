module

public import Certificates.Kernel.ONSeven.Defs
public import Certificates.Kernel.Sporadic.ON3.Words
public import CFSG.Sporadic.Schreier.ONEightNormalizersCheck

public section

namespace CertificateChecks.KernelSpor.ONEN

open CFSG.KS.TW CFSG.ONSchreier CertificateChecks.KernelSpor.ONS
open CertificateChecks.KernelSpor.ON (TT)
open CertificateChecks.KernelSpor.ON3 (invW)

@[expose] def tW (h : Nat) : List Int := Data.TWords.toList.getD h []

@[expose] def eW (j k : Nat) : List Int := (onE8Words.toList.getD j #[]).toList.getD k []

@[expose] def nW (i : Nat) : List Int := onNormWords.toList.getD i []

@[expose] noncomputable def tP (h x : Nat) : Nat := WW (tW h) x

@[expose] noncomputable def tPI (h x : Nat) : Nat := WW (invW (tW h)) x

@[expose] noncomputable def eP (j k x : Nat) : Nat := (eW j k).foldr (GZ tP tPI) x

@[expose] noncomputable def nP (i x : Nat) : Nat := WW (nW i) x

@[expose] noncomputable def nPI (i x : Nat) : Nat := WW (invW (nW i)) x

@[expose] def el8F (f g h : Nat → Nat) (x : Nat) : List Nat :=
  [x, f x, g x, f (g x), h x, f (h x), g (h x), f (g (h x))]

@[expose] noncomputable def el8 (j x : Nat) : List Nat := el8F (eP j 0) (eP j 1) (eP j 2) x

@[expose] noncomputable def ch13790A (x : Nat) : Bool :=
  Nat.beq (onAWord.foldr (GZ nP nPI) x) (TT 0 x) && Nat.beq (onBWord.foldr (GZ nP nPI) x) (TT 1 x)

@[expose] noncomputable def ch13790E (j x : Nat) : Bool :=
  Nat.beq (eP j 0 (eP j 0 x)) x && Nat.beq (eP j 1 (eP j 1 x)) x &&
    Nat.beq (eP j 2 (eP j 2 x)) x && Nat.beq (eP j 0 (eP j 1 x)) (eP j 1 (eP j 0 x)) &&
    Nat.beq (eP j 0 (eP j 2 x)) (eP j 2 (eP j 0 x)) &&
    Nat.beq (eP j 1 (eP j 2 x)) (eP j 2 (eP j 1 x))

@[expose] noncomputable def diff3 (F G : Nat → Nat) : Bool :=
  !(Nat.beq (F 0) (G 0) && Nat.beq (F 227759) (G 227759) && Nat.beq (F 100817) (G 100817))

@[expose] noncomputable def ch13790D (j : Nat) : Bool :=
  diff3 (eP j 0) id && diff3 (eP j 1) id && diff3 (eP j 1) (eP j 0) && diff3 (eP j 2) id &&
    diff3 (eP j 2) (eP j 0) && diff3 (eP j 2) (eP j 1) &&
    diff3 (eP j 2) (fun x => eP j 0 (eP j 1 x))

@[expose] noncomputable def cnj (i k x : Nat) : Nat :=
  nP i (eP (onNormTags.toList.getD i 0) k (nPI i x))

@[expose] noncomputable def ch13790N (i k : Nat) : Bool :=
  (List.range 8).any fun m =>
    Nat.beq (cnj i k 0) ((el8 (onNormTags.toList.getD i 0) 0).getD m 0) &&
    Nat.beq (cnj i k 227759) ((el8 (onNormTags.toList.getD i 0) 227759).getD m 0) &&
    Nat.beq (cnj i k 100817) ((el8 (onNormTags.toList.getD i 0) 100817).getD m 0)

end CertificateChecks.KernelSpor.ONEN

end
