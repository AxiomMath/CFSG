
module

public import Certificates.Kernel.Sporadic.OddCore.PEnumCmd
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue
public import CFSG.Sporadic.ONOddCore.SylowEightCheckInputs
meta import CFSG.Sporadic.ONOddCore.SylowEightCheckInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ON2129

open CFSG.ONSchreier CFSG.PSL3Four.Native CFSG.Sporadic.ONOddCore

meta def t32G : Array (Array Nat) := Data.T32Chain.generators

meta def id32 : Array Nat := idTab 32

meta def sqG : Array (Array Nat) := sqTabs

meta def omG : Array (Array Nat) := omegaTabs

meta def omSelM : List Nat :=
  (List.range sqEnum.tabs.size).filter fun i => comp 32 sqEnum.tabs[i]! sqEnum.tabs[i]! == idTab 32

end CertificateChecks.KernelSpor.ON2129

#kpenum CertificateChecks.KernelSpor.T32E 32 6 false CertificateChecks.KernelSpor.ON2129.t32G
  CertificateChecks.KernelSpor.ON2129.t32G CertificateChecks.KernelSpor.ON2129.id32 600

#kpenum CertificateChecks.KernelSpor.SQE 32 6 false CertificateChecks.KernelSpor.ON2129.sqG
  CertificateChecks.KernelSpor.ON2129.sqG CertificateChecks.KernelSpor.ON2129.id32 200

#kpenum CertificateChecks.KernelSpor.OME 32 6 false CertificateChecks.KernelSpor.ON2129.omG
  CertificateChecks.KernelSpor.ON2129.omG CertificateChecks.KernelSpor.ON2129.id32 20

#knatlist CertificateChecks.KernelSpor.ON2129.omSel CertificateChecks.KernelSpor.ON2129.omSelM

namespace CertificateChecks.KernelSpor.ON2129

open CFSG.ONSchreier CFSG.PSL3Four.Native CFSG.Sporadic.ONOddCore CFSG.KC.Enum CFSG.KS
open CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.Mathieu CFSG.KC.BfsPin

theorem t32_hd : penumHdK (pidn 32 6) T32E.cnt 600 T32E.T T32E.PL = true := by
  quickRfl

theorem t32_sl : penumSlK 32 6 (mask 6) (32 * 6) false T32E.G T32E.GI T32E.k T32E.cnt T32E.T
    T32E.PL T32E.POS T32E.SRT T32E.SRI 0 512 = true := by
  quickRfl

theorem t32_gens : gensK Data.T32Chain.generators 32 6 T32E.k T32E.G = true := by
  quickRfl

theorem sq_gens : allN 512 (fun j => bAnd(Nat.beq (SQE.G j)
    (pcomp 32 6 (mask 6) (T32E.T j) (T32E.T j)), canonK 32 6 (mask 6) (32 * 6) (SQE.G j))) =
    true := by
  quickRfl

theorem sq_hd : penumHdK (pidn 32 6) SQE.cnt 200 SQE.T SQE.PL = true := by
  quickRfl

theorem sq_sl : penumSlK 32 6 (mask 6) (32 * 6) false SQE.G SQE.GI SQE.k SQE.cnt SQE.T SQE.PL
    SQE.POS SQE.SRT SQE.SRI 0 64 = true := by
  quickRfl

theorem om_sel : selFrom (fun i => Nat.beq (pcomp 32 6 (mask 6) (SQE.T i) (SQE.T i)) (pidn 32 6))
    64 0 omSel = true := by
  quickRfl

theorem om_gens : allN OME.k (fun j => bAnd(Nat.beq (OME.G j) (SQE.T (nget omSel j)),
    canonK 32 6 (mask 6) (32 * 6) (OME.G j))) = true := by
  quickRfl

theorem om_hd : penumHdK (pidn 32 6) OME.cnt 20 OME.T OME.PL = true := by
  quickRfl

theorem om_sl : penumSlK 32 6 (mask 6) (32 * 6) false OME.G OME.GI OME.k OME.cnt OME.T OME.PL
    OME.POS OME.SRT OME.SRI 0 8 = true := by
  quickRfl

theorem om_facts : bAnd(allN 8 (fun a => allN 8 (fun b =>
      Nat.beq (pcomp 32 6 (mask 6) (OME.T a) (OME.T b)) (pcomp 32 6 (mask 6) (OME.T b) (OME.T a)))),
    bAnd(allN 8 (fun a => Nat.beq (pcomp 32 6 (mask 6) (OME.T a) (OME.T a)) (pidn 32 6)),
    bAnd(canonK 32 6 (mask 6) (32 * 6) (pidn 32 6), idK 32 6 (mask 6)))) = true := by
  quickRfl

end CertificateChecks.KernelSpor.ON2129

end
