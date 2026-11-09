module

public import Certificates.Kernel.Y63.Par
public import Certificates.Kernel.Y63.Split

public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace CertificateChecks.KernelY63

open CFSG.OddStandard.HigherRank.YamadaG23.Y63Chk

theorem par_ok : ParOK dK parY letY := by decide +kernel

theorem mulr_0 : allB 128 (fun i => mulRowB dK parY letY (128 * 0 + i)) = true := by
  decide +kernel

theorem mulr_1 : allB 128 (fun i => mulRowB dK parY letY (128 * 1 + i)) = true := by
  decide +kernel

theorem mulr_2 : allB 128 (fun i => mulRowB dK parY letY (128 * 2 + i)) = true := by
  decide +kernel

theorem mulr_3 : allB 128 (fun i => mulRowB dK parY letY (128 * 3 + i)) = true := by
  decide +kernel

theorem mul : dK.MulSpec :=
  MulSpec_of_par par_ok
    (ball_blocks (N := 128) (B := 4) (P := fun x => mulRowB dK parY letY x = true)
      fun j hj => match j, hj with
      | 0, _ => allB_iff.1 mulr_0
      | 1, _ => allB_iff.1 mulr_1
      | 2, _ => allB_iff.1 mulr_2
      | 3, _ => allB_iff.1 mulr_3
      | _ + 4, h => absurd h (by omega))

end CertificateChecks.KernelY63

end
