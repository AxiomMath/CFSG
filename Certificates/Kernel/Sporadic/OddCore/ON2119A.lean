module

public import Certificates.Kernel.Sporadic.OddCore.ON2129F
public import Certificates.Kernel.Sporadic.OddCore.PEnumFamCmd
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue2
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue3
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Sporadic.ONOddCore.InvolutionCheckInputs
meta import CFSG.Sporadic.ONOddCore.InvolutionCheckInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.SmallOddCore.ClassSimple

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ON2119

open CFSG.PSL3Four.Native CFSG.Sporadic.ONOddCore CFSG.ONSchreier

meta def gM : Array (Array Nat) := Data.T32Chain.generators
meta def giM : Array (Array Nat) := Data.T32Chain.generators.map (invTab 32)
meta def rootsM : Array (Array Nat) := repTabs32

meta def coverM : Array (Array Nat) :=
  let idxs := repOrbits32.map fun e => indexOf e.tabs
  t32Enum.tabs.map fun t =>
    if t == idTab 32 then #[0]
    else if !(comp 32 t t == idTab 32) then #[1]
    else
      let l := ((List.range 7).find? fun l => (idxs[l]!).contains t).getD 0
      #[2 + 65536 * l + (idxs[l]!).getD t 0]

end CertificateChecks.KernelSpor.ON2119

#kmisc_packarrs CertificateChecks.KernelSpor.T32I CertificateChecks.KernelSpor.ON2119.giM 6
#kpenumfam CertificateChecks.KernelSpor.T32O 32 6 true CertificateChecks.KernelSpor.ON2119.gM
  CertificateChecks.KernelSpor.ON2119.giM CertificateChecks.KernelSpor.ON2119.rootsM 64
#kmisc_packarrs CertificateChecks.KernelSpor.T32COV CertificateChecks.KernelSpor.ON2119.coverM 32

namespace CertificateChecks.KernelSpor.ON2119

open CFSG.PSL3Four.Native CFSG.Sporadic.ONOddCore CFSG.ONSchreier CFSG.KC.Enum CFSG.KS
open CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KC.Misc.HexAt CFSG.Monster.B.Co2.Native
open CertificateChecks.KernelSpor.ON2129

theorem inv_ok : allN 6 (fun j => bAnd(invEqK 32 6 (mask 6) (32 * 6) (T32E.G j) (T32I j),
    bAnd(canonK 32 6 (mask 6) (32 * 6) (T32I j),
    bAnd(Nat.beq (pcomp 32 6 (mask 6) (T32I j) (T32E.G j)) (pidn 32 6),
    bAnd(Nat.beq (T32O.G j) (T32E.G j), Nat.beq (T32O.GI j) (T32I j)))))) = true := by
  quickRfl

theorem reps_ok : allN 7 (fun l => bAnd(Nat.beq (T32O.R l)
    (wordTabK 32 6 (mask 6) (pidn 32 6) T32E.G (lget2 repWords.toList l)),
    penumHdK (T32O.R l) (T32O.C l) 64 (offF T32O.T (T32O.TO l)) (offF T32O.PL (T32O.PLO l)))) =
    true := by
  quickRfl

theorem orb_sl : allN 7 (fun l => penumSlK 32 6 (mask 6) (32 * 6) true T32O.G T32O.GI T32O.k
    (T32O.C l) (offF T32O.T (T32O.TO l)) (offF T32O.PL (T32O.PLO l)) (offF T32O.POS (T32O.POSO l))
    (offF T32O.SRT (T32O.SRTO l)) (offF T32O.SRI (T32O.SRIO l)) 0 64) = true := by
  quickRfl

@[expose] noncomputable def coverK (k : Nat) : Bool :=
  strictB (T32COV k) (fun wk =>
    bIf(Nat.beq wk 0, Nat.beq (T32E.T k) (pidn 32 6),
    bIf(Nat.beq wk 1, bIf(Nat.beq (pcomp 32 6 (mask 6) (T32E.T k) (T32E.T k)) (pidn 32 6),
      false, true),
      strictB (Nat.sub wk 2) (fun c => strictB (Nat.shiftRight c 16) (fun l =>
        strictB (Nat.land c 65535) (fun q => bAnd(Nat.blt l 7, bAnd(Nat.blt q (T32O.C l),
          Nat.beq (offF T32O.T (T32O.TO l) q) (T32E.T k)))))))))

theorem cover_ok : allN 512 coverK = true := by
  quickRfl

end CertificateChecks.KernelSpor.ON2119

end
