module

public import Certificates.Kernel.Misc.Sp6RefS.Data
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelMisc.Sp6RefS

open CFSG.KD.Sp6RefS

theorem sp6refs_a_ok : aK ZG AX = true := by quickRfl

theorem sp6refs_add_ok : aAddK AX = true := by quickRfl

theorem sp6refs_w_ok : wK WG WX WP WC = true := by quickRfl

theorem sp6refs_wm_ok : wmK ZG AX WX WM = true := by quickRfl

theorem sp6refs_frame_ok : frameK ZG AX WX FR = true := by quickRfl

theorem sp6refs_look_ok : lookK AX WX QI RT RS RI RW = true := by quickRfl

theorem sp6refs_c7_ok : c7K CG CX CP CS W7 = true := by quickRfl

theorem sp6refs_orb_ok : orbK HG HI OX OP OS W7 = true := by quickRfl

theorem sp6refs_r0_ok : rTabK RG0 (rqX 0) (rqP 0) RC 3 8 (RS 0) (AX (RI 0)) = true := by quickRfl

theorem sp6refs_r1_ok : rTabK (fun _ => RS 1) (rqX 8) (rqP 8) (fun i => RC (Nat.add 32 i)) 1 2 (RS 1)
    (AX (RI 1)) = true := by quickRfl

theorem sp6refs_r2_ok : rTabK RG2 (rqX 10) (rqP 10) (fun i => RC (Nat.add 36 i)) 3 8 (RS 2)
    (AX (RI 2)) = true := by quickRfl

theorem sp6refs_r3_ok : rTabK (fun _ => RS 3) (rqX 18) (rqP 18) (fun i => RC (Nat.add 68 i)) 1 2
    (RS 3) (AX (RI 3)) = true := by quickRfl

theorem sp6refs_r4_ok : rTabK RG4 (rqX 20) (rqP 20) (fun i => RC (Nat.add 72 i)) 2 8 (RS 4)
    (AX (RI 4)) = true := by quickRfl

theorem sp6refs_ab_ok : (abK (rqX 0) 8 && abK (rqX 10) 8 && !(commB (RG4 0) (RG4 1))) = true := by
  quickRfl

theorem sp6refs_sl_ok : slK HG HI 8 44097 (AX 12) (WG 2) = true := by quickRfl

theorem sp6refs_rep0_ok : repK (recS 38) RG0 (rqX 0) RR 2160 34 3 8 (RS 0) = true := by quickRfl

theorem sp6refs_rep1_ok : repK (recS 6521) (fun _ => RS 1) (rqX 8) (fun p => RR (Nat.add 2160 p))
    108 2 1 2 (RS 1) = true := by quickRfl

theorem sp6refs_rep2_ok : repK (recS 4360) RG2 (rqX 10) (fun p => RR (Nat.add 2268 p)) 2160 34 3 8
    (RS 2) = true := by quickRfl

theorem sp6refs_rep3_ok : repK (recS 6521) (fun _ => RS 3) (rqX 18) (fun p => RR (Nat.add 4428 p))
    108 2 1 2 (RS 3) = true := by quickRfl

theorem sp6refs_rep4_ok : repK (fun p => CX (CS p)) RG4 (rqX 20) (fun p => RR (Nat.add 4536 p)) 648 11
    2 8 (RS 4) = true := by quickRfl

end CertificateChecks.KernelMisc.Sp6RefS
