module

public import Certificates.Kernel.Sporadic.Fi22.B9551Chk
public import Certificates.Kernel.Sporadic.Fi22.FiveK
public import Certificates.Kernel.Sporadic.Fi22.N3153Final
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.B9551

open CFSG.KC.Enum CFSG.KC.N3153 CFSG.KD.N3153 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
open CFSG.Sporadic.FischerOddCore CFSG.Sporadic.FischerOddCore.Native
open CFSG.AGLEmbedding.KFactProofs.Fi22Five CFSG.AGLEmbedding.KFactProofs.Fi22Guest
open CFSG.Monster.B.Fischer CertificateChecks.KernelSpor

theorem ux0 : UX 0 = Fi22W.W (signedWord wx) := Nat.eq_of_beq_eq_true (by quickRfl)

theorem xu_eq : xA = unpack 3510 12 (UX 0) := by
  rw [ux0]
  exact Fi22FiveK.x_eq

theorem cell_of {s : Nat} (hs : s < fivePts.length) :
    cellK 3510 S (UX 0) fivePts 4 s (fiveBounds.getD s 0) = true :=
  Cell.all s (by simpa [fivePts] using hs)

theorem inj_of : injK 3510 S (UX 0) fivePts 4 (CFSG.KD.N9551.O 0) = true :=
  Inj.all 0 (by norm_num)

theorem bound :
    boundCheck = true := by
  have h : boundsOK 3510 fi22Nbr xA fivePts fiveBounds 4 = true :=
    bounds_sound (d := 693) (R := R) (M := M) (S := S) (T := UX 0) (P := CFSG.KD.N9551.O 0)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) N3153.nbr_eq N3153.rows N3153.symm
      xu_eq rfl (by decide) (fun _ hs => cell_of hs) inj_of
  unfold boundCheck
  rw [h]
  decide

end CertificateChecks.KernelSpor.B9551

end
