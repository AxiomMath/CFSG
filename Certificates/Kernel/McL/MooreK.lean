module

public import CFSG.Certificates.Kernel.Spor.PackWord
public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Sporadic.SmallOddCore.McLLocalCheckInputs
public import CFSG.Sporadic.Recognition.McLCentralizerInputs
meta import CFSG.Sporadic.SmallOddCore.McLLocalCheckInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelMcL.MoCT CFSG.Sporadic.SmallOddCore.mclCentHex

#kmisc_hexflat CertificateChecks.KernelMcL.MoCT CFSG.Sporadic.SmallOddCore.mclCentHex 3 275 9 30

namespace CertificateChecks.KernelMcL.Moore

open CFSG.Sporadic.SmallOddCore

meta def fixM : List Nat := mclFix

meta def xgM : Array (Array Nat) := mclXGens

end CertificateChecks.KernelMcL.Moore

#knatlist CertificateChecks.KernelMcL.Moore.fixL CertificateChecks.KernelMcL.Moore.fixM

#kmisc_packarrs CertificateChecks.KernelMcL.MoXG CertificateChecks.KernelMcL.Moore.xgM 6

namespace CertificateChecks.KernelMcL.Moore

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.Mathieu
open CFSG.Sporadic.Recognition.McLCentralizer

@[expose] noncomputable def xP (i : Nat) : Nat :=
  wordTabK 35 6 (mask 6) (pidn 35 6) MoXG (mooreWord i)

@[expose] noncomputable def liftP : Nat :=
  wordTabK 275 9 (mask 9) (pidn 275 9) (fun j => MoCT.F (Nat.add j 5)) (mooreWord 4)

theorem fix_sel : selFrom (fun x => Nat.beq (pg 9 (mask 9) (MoCT.F 4) x) x) 275 0 fixL = true := by
  quickRfl

theorem xg_ok : allN 2 (fun k => bAnd(canonK 35 6 (mask 6) (35 * 6) (MoXG k),
    allN 35 (fun a => Nat.beq (pg 9 (mask 9) (MoCT.F (Nat.add k 5)) (nget fixL a))
      (nget fixL (pg 6 (mask 6) (MoXG k) a))))) = true := by
  quickRfl

theorem id35 : bAnd(canonK 35 6 (mask 6) (35 * 6) (pidn 35 6), idK 35 6 (mask 6)) = true := by
  quickRfl

theorem id275 : bAnd(canonK 275 9 (mask 9) (275 * 9) (pidn 275 9), idK 275 9 (mask 9)) = true := by
  quickRfl

theorem c275 : bAnd(canonK 275 9 (mask 9) (275 * 9) (MoCT.F 5),
    canonK 275 9 (mask 9) (275 * 9) (MoCT.F 6)) = true := by
  quickRfl

theorem m1 : Nat.beq (pcomp 35 6 (mask 6) (xP 1) (pcomp 35 6 (mask 6) (xP 1) (xP 1)))
    (pidn 35 6) = true := by
  quickRfl

theorem m2 : (List.range' 2 5).all (fun j =>
    Nat.beq (pcomp 35 6 (mask 6) (xP j) (xP j)) (pidn 35 6) &&
      Nat.beq (pcomp 35 6 (mask 6) (pcomp 35 6 (mask 6) (xP (j - 1)) (xP j))
        (pcomp 35 6 (mask 6) (pcomp 35 6 (mask 6) (xP (j - 1)) (xP j))
          (pcomp 35 6 (mask 6) (xP (j - 1)) (xP j)))) (pidn 35 6)) = true := by
  quickRfl

theorem m3 : (List.range' 1 4).all (fun i => (List.range' (i + 2) (5 - i)).all fun j =>
    Nat.beq (pcomp 35 6 (mask 6) (pcomp 35 6 (mask 6) (xP i) (xP j))
      (pcomp 35 6 (mask 6) (xP i) (xP j))) (pidn 35 6)) = true := by
  quickRfl

theorem lift : Nat.beq (pcomp 275 9 (mask 9) liftP liftP) (MoCT.F 4) = true := by
  quickRfl

end CertificateChecks.KernelMcL.Moore

end
