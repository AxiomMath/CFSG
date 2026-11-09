module

public import Certificates.Kernel.Y63.Data

public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace CertificateChecks.KernelY63

open CFSG.OddStandard.HigherRank.YamadaG23.Y63Chk

theorem q2 : dK.QSpec 2 :=
  ⟨by decide +kernel,
    cenSpec_of_gens [dK.T 0 0, dK.T 0 2, dK.T 0 4, dK.T 0 6, dK.T 0 8, 512] (by decide +kernel)
      (by decide +kernel),
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
      uClos_of_pos (f10 (U0T 2)) (fun i j => f7u (UPT (256 + i)) j) rfl (by decide +kernel),
      by decide +kernel, by decide +kernel, czAll_of (f10 (U0T 2)) rfl (by decide +kernel),
      uMax_of 288 (f10 (USQT 2)) (fun i => f10 (WZT 2) (2 * i)) (fun i => f10 (WZT 2) (2 * i + 1))
        (by decide +kernel) (by decide +kernel)⟩,
    candSpec_of (by decide +kernel) (by decide +kernel)⟩

theorem q3 : dK.QSpec 3 :=
  ⟨by decide +kernel,
    cenSpec_of_gens [dK.T 0 0, dK.T 0 2, dK.T 0 4, dK.T 0 6, dK.T 0 8, 512] (by decide +kernel)
      (by decide +kernel),
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
      uClos_of_pos (f10 (U0T 3)) (fun i j => f7u (UPT (384 + i)) j) rfl (by decide +kernel),
      by decide +kernel, by decide +kernel, czAll_of (f10 (U0T 3)) rfl (by decide +kernel),
      uMax_of 288 (f10 (USQT 3)) (fun i => f10 (WZT 3) (2 * i)) (fun i => f10 (WZT 3) (2 * i + 1))
        (by decide +kernel) (by decide +kernel)⟩,
    candSpec_of (by decide +kernel) (by decide +kernel)⟩

end CertificateChecks.KernelY63

end
