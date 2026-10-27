module

public import Certificates.Data.Kernel.DceS5
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Data.Sel
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Checks.C_0
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Checks.C_1
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Checks.C_2
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Checks.C_3
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Checks.C_4
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Checks.ES1_0
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Checks.ES1_1
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Checks.ES1_2
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Checks.ES1_3
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Checks.ES1_4
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Checks.ES2_0
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Checks.ES3_0
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Checks.ES4_0
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Checks.G_0
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Checks.H_0
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Checks.OS_0
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Checks.S1_0
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Checks.S1_1
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Checks.S1_2
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Checks.S1_3
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Checks.S1_4
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Checks.S2_0
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Checks.S3_0
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Checks.S4_0
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Checks.TS_0
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Checks.TS_1
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Checks.TS_2
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Checks.TS_3
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Checks.TS_4
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Checks.T_0
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Checks.T_1
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Checks.T_2
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Checks.T_3
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Checks.T_4
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Checks.T_5
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Checks.T_6
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Checks.T_7
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Checks.W_0
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Checks.W_1
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Checks.W_2
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Checks.W_3
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Checks.W_4
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Checks.W_5
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Checks.W_6
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Checks.W_7
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Checks.W_8
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Checks.W_9
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Checks.X_0
import Certificates.Kernel.DceS5.Assemble

public section

#loop_join CertificateChecks.KernelBounds.Ly.facts CFSG.Certificates.DS5.runFacts_append CFSG.KD.LyA.w 0 440
#loop_join CertificateChecks.KernelBounds.Ly.hdr CFSG.Certificates.DS5.runHdr_append CFSG.KD.LyA.h 0 20
#loop_join CertificateChecks.KernelBounds.Ly.gom CFSG.Certificates.DS5.runGom_append CFSG.KD.LyA.g 0 40
#loop_join CertificateChecks.KernelBounds.Ly.os CFSG.Certificates.DS5.runSorted_append CFSG.KD.LyA.os 0 7
#loop_join CertificateChecks.KernelBounds.Ly.ts CFSG.Certificates.DS5.runSorted_append CFSG.KD.LyA.ts 0 100
#loop_join CertificateChecks.KernelBounds.Ly.tab CFSG.Certificates.DS5.runT_append CFSG.KD.LyA.t 0 200
#loop_join CertificateChecks.KernelBounds.Ly.cover CFSG.Certificates.DS5.runCover_append CFSG.KD.LyA.c 0 98
#loop_join CertificateChecks.KernelBounds.Ly.sj1 CFSG.Certificates.DS5.runStab_append CFSG.KD.LyA.s1 0 100
#loop_join CertificateChecks.KernelBounds.Ly.ej1 CFSG.Certificates.DS5.runSorted_append CFSG.KD.LyA.es1 0 100
#loop_join CertificateChecks.KernelBounds.Ly.sj2 CFSG.Certificates.DS5.runStab_append CFSG.KD.LyA.s2 0 3
#loop_join CertificateChecks.KernelBounds.Ly.ej2 CFSG.Certificates.DS5.runSorted_append CFSG.KD.LyA.es2 0 3
#loop_join CertificateChecks.KernelBounds.Ly.sj3 CFSG.Certificates.DS5.runStab_append CFSG.KD.LyA.s3 0 1
#loop_join CertificateChecks.KernelBounds.Ly.ej3 CFSG.Certificates.DS5.runSorted_append CFSG.KD.LyA.es3 0 1
#loop_join CertificateChecks.KernelBounds.Ly.sj4 CFSG.Certificates.DS5.runStab_append CFSG.KD.LyA.s4 0 1
#loop_join CertificateChecks.KernelBounds.Ly.ej4 CFSG.Certificates.DS5.runSorted_append CFSG.KD.LyA.es4 0 1

#ds5_ok CertificateChecks.KernelBounds.Ly.dce_ok CFSG.KD.LyA CertificateChecks.KernelBounds.Ly
  CertificateChecks.KernelBounds.Ly.facts CertificateChecks.KernelBounds.Ly.hdr
  CertificateChecks.KernelBounds.Ly.gom CertificateChecks.KernelBounds.Ly.os
  CertificateChecks.KernelBounds.Ly.ts CertificateChecks.KernelBounds.Ly.tab
  CertificateChecks.KernelBounds.Ly.cover [1, 2, 3, 4]

end
