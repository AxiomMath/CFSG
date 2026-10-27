module

public import Certificates.Kernel.SuzA17321.Checks
public import Certificates.Kernel.SuzThree13637.HypData
public import Certificates.Data.TabSuzFuse
public import Certificates.Data.Kernel.Spor.PSearch
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelSuzFuse17320

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.B3S3K
open CertificateChecks.KernelSpor CertificateChecks.KernelSuzPump CertificateChecks.KernelSuzA17321
open CFSG.HardMathSupport.Dickson.I271.TabSuzFuse
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT (digit3)

@[expose] noncomputable def XB : Nat := (reb xBTuple).1

@[expose] noncomputable def DK (i : Nat) : Nat := CFSG.KS.PSearch.nthN CFSG.KD.SuzThree13637.F.D i

@[expose] noncomputable def pw3 (g e : Nat) : Nat := ppow 1782 11 (mask 11) (pidn 1782 11) g e

@[expose] noncomputable def EP (k : Nat) : Nat :=
  pcomp 1782 11 (mask 11) (pw3 (DK 0) (digit3 k 0)) (pcomp 1782 11 (mask 11) (pw3 (DK 1) (digit3 k 1))
    (pcomp 1782 11 (mask 11) (pw3 (DK 2) (digit3 k 2)) (pcomp 1782 11 (mask 11)
      (pw3 (DK 3) (digit3 k 3)) (pw3 (DK 4) (digit3 k 4)))))

@[expose] noncomputable def HK (k : Nat) : Nat := (reb fuseTuples[k]!).1

@[expose] noncomputable def tgt (k : Nat) : Nat := bif fuseCls[k]! == 0 then XP else XB

@[expose] noncomputable def fuseKT (k G T : Nat) : Bool :=
  permB 1782 11 G && siftPK G &&
    Nat.beq (pcomp 1782 11 (mask 11) G (pcomp 1782 11 (mask 11) (EP k) (pinvS 1782 11 (mask 11) G)))
      T

@[expose] noncomputable def fuseK (k : Nat) : Bool :=
  (reb fuseTuples[k]!).2.2 && fuseKT k (HK k) (tgt k)

@[expose] noncomputable def fuseS (j : Nat) : Bool := allN 22 (fun i => fuseK (22 * j + i + 1))

theorem rbB : (reb xBTuple).2.2 = true := by quickRfl

theorem pXB : permB 1782 11 XB = true := by quickRfl

theorem pD : allN 5 (fun i => permB 1782 11 (DK i)) = true := by quickRfl

theorem siftX : siftPK XP = true ∧ siftPK XB = true := ⟨by quickRfl, by quickRfl⟩

theorem ordX : Nat.beq (pw3 XP 3) (pidn 1782 11) = true ∧ Nat.beq XP (pidn 1782 11) = false ∧
    Nat.beq (pw3 XB 3) (pidn 1782 11) = true ∧ Nat.beq XB (pidn 1782 11) = false :=
  ⟨by quickRfl, by decide +kernel, by quickRfl, by decide +kernel⟩

theorem s0 : fuseS 0 = true := by quickRfl
theorem s1 : fuseS 1 = true := by quickRfl
theorem s2 : fuseS 2 = true := by quickRfl
theorem s3 : fuseS 3 = true := by quickRfl
theorem s4 : fuseS 4 = true := by quickRfl
theorem s5 : fuseS 5 = true := by quickRfl
theorem s6 : fuseS 6 = true := by quickRfl
theorem s7 : fuseS 7 = true := by quickRfl
theorem s8 : fuseS 8 = true := by quickRfl
theorem s9 : fuseS 9 = true := by quickRfl
theorem s10 : fuseS 10 = true := by quickRfl

end CertificateChecks.KernelSuzFuse17320

end
