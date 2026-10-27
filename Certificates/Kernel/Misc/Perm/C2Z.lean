module

public import Certificates.Kernel.Misc.Perm.C2N
public import CFSG.Certificates.Kernel.Co2Five.LitStructures

public section

namespace CertificateChecks.KernelMisc.Co2K

open CFSG.RankThree.Native CFSG.RankThree.Native.Co2FiveLit

theorem litChecks : Co2FiveLitChecks :=
  ⟨chain_ok litC0.1 litC0.2.1, qcheck_ok, c0check_ok,
    ⟨enumC1, litC1.1, enumD, litD.1, c1_comm, d_rel, d_conj, d_comm, d_nonab, d_words, d_cent,
      t_valid⟩⟩

end CertificateChecks.KernelMisc.Co2K

end
