module

public import Certificates.Kernel.Y63.Data

public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace CertificateChecks.KernelY63

open CFSG.OddStandard.HigherRank.YamadaG23.Y63Chk

theorem q0 : dK.QSpec 0 :=
  ⟨by decide +kernel,
    cenSpec_of_gens [dK.T 0 0, dK.T 0 2, dK.T 0 4, dK.T 0 6, dK.T 0 8, 512] (by decide +kernel)
      (by decide +kernel),
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
      uClos_of_pos (f10 (U0T 0)) (fun i j => f7u (UPT i) j) rfl (by decide +kernel),
      by decide +kernel, by decide +kernel, czAll_of (f10 (U0T 0)) rfl (by decide +kernel),
      uMax_of 288 (f10 (USQT 0)) (fun i => f10 (WZT 0) (2 * i)) (fun i => f10 (WZT 0) (2 * i + 1))
        (by decide +kernel) (by decide +kernel)⟩,
    candSpec_of (by decide +kernel) (by decide +kernel)⟩

theorem q1 : dK.QSpec 1 :=
  ⟨by decide +kernel,
    cenSpec_of_gens [dK.T 0 0, dK.T 0 2, dK.T 0 4, dK.T 0 6, dK.T 0 8, 512] (by decide +kernel)
      (by decide +kernel),
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
      uClos_of_pos (f10 (U0T 1)) (fun i j => f7u (UPT (128 + i)) j) rfl (by decide +kernel),
      by decide +kernel, by decide +kernel, czAll_of (f10 (U0T 1)) rfl (by decide +kernel),
      uMax_of 288 (f10 (USQT 1)) (fun i => f10 (WZT 1) (2 * i)) (fun i => f10 (WZT 1) (2 * i + 1))
        (by decide +kernel) (by decide +kernel)⟩,
    candSpec_of (by decide +kernel) (by decide +kernel)⟩

end CertificateChecks.KernelY63

end
