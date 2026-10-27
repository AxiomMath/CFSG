module

public import Certificates.Data.Kernel.YoshQ.Replay
public meta import Certificates.Kernel.YoshQ.Gen
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Certificates.Kernel.Common.Eval

public section

#kc_eval CertificateChecks.KernelYoshQ E00 CertificateChecks.KernelYoshQ.stepW 0 0 0
#kc_eval CertificateChecks.KernelYoshQ E01 CertificateChecks.KernelYoshQ.stepW 0 1 0
#kc_eval CertificateChecks.KernelYoshQ E10 CertificateChecks.KernelYoshQ.stepW 1 0 0
#kc_eval CertificateChecks.KernelYoshQ E11 CertificateChecks.KernelYoshQ.stepW 1 1 0
#kc_eval CertificateChecks.KernelYoshQ S00 CertificateChecks.KernelYoshQ.stepW 0 0 1
#kc_eval CertificateChecks.KernelYoshQ S01 CertificateChecks.KernelYoshQ.stepW 0 1 1
#kc_eval CertificateChecks.KernelYoshQ S10 CertificateChecks.KernelYoshQ.stepW 1 0 1
#kc_eval CertificateChecks.KernelYoshQ S11 CertificateChecks.KernelYoshQ.stepW 1 1 1
#kc_eval CertificateChecks.KernelYoshQ A10 CertificateChecks.KernelYoshQ.stepW 1 0 2
#kc_eval CertificateChecks.KernelYoshQ A11 CertificateChecks.KernelYoshQ.stepW 1 1 2

end
