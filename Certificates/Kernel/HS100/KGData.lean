module

public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.HS100.ChainData
public import Certificates.Data.Kernel.BfsPinBase
public import Certificates.Data.Kernel.Misc.ArrEnum
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.KGHS3HSDataA
meta import CFSG.LocalAnalysis.ComponentClassification.CatFC.KGHS3HSDataA
meta import Certificates.Kernel.Sporadic.RawGen
import CFSG.Certificates.Kernel.Common.Harness

namespace CertificateChecks.KernelHS100.KGE

open CFSG.ComponentClassification.CatFC.KGHS3

meta def all : Array (Array Nat) :=
  #[hsA3Arr, hsB3Arr, hsG3Arr, hsX5Arr, hsY5Arr, hsG5Arr, hsU11Arr, hsH11Arr]

end CertificateChecks.KernelHS100.KGE

public section

set_option maxRecDepth 400000

#kmisc_packarrs CertificateChecks.KernelHS100.KG CertificateChecks.KernelHS100.KGE.all 7

namespace CertificateChecks.KernelHS100

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum
open CFSG.ComponentClassification.CatFC.KGHS3

@[expose] noncomputable def kgMul (p q : ℕ) : ℕ := pcomp 100 7 (mask 7) p q

@[expose] noncomputable def kgInv (p : ℕ) : ℕ := pinvS 100 7 (mask 7) p

@[expose] noncomputable def kgPw (p e : ℕ) : ℕ := ppow 100 7 (mask 7) (pidn 100 7) p e

@[expose] noncomputable def kgZ (x y : ℕ) : ℕ := kgMul (kgMul (kgMul x y) (kgInv x)) (kgInv y)

theorem KG.bind : (arrBind hsA3Arr 100 7 (KG 0) && arrBind hsB3Arr 100 7 (KG 1) &&
    arrBind hsG3Arr 100 7 (KG 2) && arrBind hsX5Arr 100 7 (KG 3) &&
    arrBind hsY5Arr 100 7 (KG 4) && arrBind hsG5Arr 100 7 (KG 5) &&
    arrBind hsU11Arr 100 7 (KG 6) && arrBind hsH11Arr 100 7 (KG 7)) = true := by quickRfl

theorem KG.perm : allN 8
    (fun j => permOK 100 7 (mask 7) (100 * 7) (KG j) (pinvS 100 7 (mask 7) (KG j))) = true := by
  quickRfl

theorem KG.sift : allN 8 (fun j => Nat.beq (Nat.shiftRight (KG j) (100 * 7)) 0 &&
    allN 100 (fun t => Nat.blt (pg 7 (mask 7) (KG j) t) 100) &&
    siftK 100 7 (mask 7) (100 * 7) (pidn 100 7) HC.LR HC.TRI HC.BP 5 0 (KG j)) = true := by
  quickRfl

@[expose] noncomputable def kgC3 (a b g : ℕ) : Bool :=
  Nat.beq (kgPw a 3) (pidn 100 7) && Nat.beq (kgPw b 3) (pidn 100 7) &&
    !Nat.beq a (pidn 100 7) && Nat.beq (kgMul a b) (kgMul b a) &&
    Nat.beq (kgMul g a) (kgMul b g) && Nat.beq (kgMul g b) (kgMul (kgMul a b) g)

@[expose] noncomputable def kgC5 (x y g z : ℕ) : Bool :=
  Nat.beq (kgPw z 5) (pidn 100 7) && !Nat.beq z (pidn 100 7) &&
    Nat.beq (kgMul x z) (kgMul z x) && Nat.beq (kgMul y z) (kgMul z y) &&
    Nat.beq (kgMul g z) (kgMul (kgPw z 2) g)

@[expose] noncomputable def kgC11 (u h : ℕ) : Bool :=
  Nat.beq (kgPw u 11) (pidn 100 7) && !Nat.beq u (pidn 100 7) &&
    Nat.beq (kgMul h u) (kgMul (kgPw u 3) h)

theorem KG.c3 : kgC3 (KG 0) (KG 1) (KG 2) = true := by quickRfl

theorem KG.c5 : kgC5 (KG 3) (KG 4) (KG 5) (kgZ (KG 3) (KG 4)) = true := by quickRfl

theorem KG.c11 : kgC11 (KG 6) (KG 7) = true := by quickRfl

end CertificateChecks.KernelHS100

end
