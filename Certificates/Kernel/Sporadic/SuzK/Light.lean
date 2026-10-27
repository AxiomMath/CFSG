module

public import Certificates.Kernel.Sporadic.SuzK.LaneDefs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Spor.F3R

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzK

open CFSG.F3.Native CFSG.KS CFSG.KS.F3L CFSG.KS.F3R CFSG.KC.Enum CFSG.Sporadic.Suz.Native

set_option Elab.async false

theorem seedA_ok : seedK (nat_lit 64) (ln 0) SeedA.chars = true := by quickRfl
theorem seedB_ok : seedK (nat_lit 64) (ln 1) SeedB.chars = true := by quickRfl

theorem canon_ok : bAnd(canonF (ln 0), bAnd(canonF (ln 1), bAnd(canonF (ln 2), bAnd(canonF (ln 3),
    bAnd(canonF (ln 4), bAnd(canonF (ln 5), bAnd(canonF (ln 6), bAnd(canonF (ln 7),
    bAnd(canonF (ln 8), canonF (mulF (ln 0) (ln 1))))))))))) = true := by quickRfl

theorem canonK_ok : bAnd(canonF (laneK 0), bAnd(canonF (laneK 1), bAnd(canonF (laneK 2),
    bAnd(canonF (laneK 3), bAnd(canonF (laneK 4), canonF (laneK 5)))))) = true := by quickRfl

theorem id_ok : eqMK 64 (idM 64) (unlane 64 (ln 3)) = true := by decide +kernel
theorem formF_ok : eqMK 64 (formF ()) (unlane 64 (ln 4)) = true := by decide +kernel
theorem formP_ok : eqMK 64 (formP ()) (unlane 64 (ln 5)) = true := by decide +kernel
theorem formPinv_ok : eqMK 64 (formPinv ()) (unlane 64 (ln 6)) = true := by decide +kernel
@[expose] noncomputable def diagDK : Array V :=
  Array.ofFn (n := 64) fun i => ofFnK 64 fun j => if j = i.val then formD[i.val]! else 0

theorem diagD_ok : eqMK 64 diagDK (unlane 64 (ln 7)) = true := by decide +kernel
theorem rootL_ok : eqMK 64 (rootRows ()) (unlane 64 (ln 8)) = true := by decide +kernel
theorem canonLit_ok : (canonMK 64 (formF ()) && canonMK 64 (formP ()) &&
    canonMK 64 (formPinv ()) && canonMK 64 diagDK && canonMK 64 (rootRows ())) = true := by
  decide +kernel
theorem wfLit_ok : (wfMK (formF ()) && wfMK (formP ()) && wfMK (formPinv ()) &&
    (formF ()).size == 64 && (formP ()).size == 64 && (formPinv ()).size == 64) = true := by
  decide +kernel

theorem consts_ok : CFSG.KC.Ord.consts3OK 64 8 4096 LO RM CI ONE UP = true := by quickRfl
theorem vld_ok : bAnd(VLD (x3 0), VLD (x3 1)) = true := by quickRfl

theorem a2_ok : eqF (mulF (ln 0) (ln 0)) (ln 3) = true := by quickRfl
theorem bb2_ok : eqF (mulF (ln 1) (ln 2)) (ln 3) = true := by quickRfl
theorem b2_ok : eqF (mulF (ln 1) (ln 1)) (ln 2) = true := by quickRfl
theorem b3_ok : eqF (powF (ln 1) 3) (ln 3) = true := by quickRfl
theorem ab13_ok : eqF (powF (mulF (ln 0) (ln 1)) 13) (ln 3) = true := by quickRfl
theorem ne_ok : bAnd(Bool.not (eqF (ln 0) (ln 3)), bAnd(Bool.not (eqF (ln 1) (ln 3)),
    Bool.not (eqF (mulF (ln 0) (ln 1)) (ln 3)))) = true := by quickRfl

theorem fA_ok : eqF (mulF (trLane 64 (ln 0)) (mulF (ln 4) (ln 0))) (ln 4) = true := by quickRfl
theorem fB_ok : eqF (mulF (trLane 64 (ln 1)) (mulF (ln 4) (ln 1))) (ln 4) = true := by quickRfl
theorem fP_ok : eqF (mulF (trLane 64 (ln 5)) (mulF (ln 4) (ln 5))) (ln 7) = true := by quickRfl
theorem fPi_ok : eqF (mulF (ln 6) (ln 5)) (ln 3) = true := by quickRfl

end CertificateChecks.KernelSpor.SuzK

end
