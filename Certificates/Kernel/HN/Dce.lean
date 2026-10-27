module

public import Certificates.Data.Kernel.DceSP
public import CFSG.Certificates.Kernel.Bounds.HNAlt.Data.Sel
public import CFSG.Certificates.Kernel.Bounds.HNAlt.Checks.C_0
public import CFSG.Certificates.Kernel.Bounds.HNAlt.Checks.C_1
public import CFSG.Certificates.Kernel.Bounds.HNAlt.Checks.ES_0
public import CFSG.Certificates.Kernel.Bounds.HNAlt.Checks.G_0
public import CFSG.Certificates.Kernel.Bounds.HNAlt.Checks.H_0
public import CFSG.Certificates.Kernel.Bounds.HNAlt.Checks.OS_0
public import CFSG.Certificates.Kernel.Bounds.HNAlt.Checks.S_0
public import CFSG.Certificates.Kernel.Bounds.HNAlt.Checks.TS_0
public import CFSG.Certificates.Kernel.Bounds.HNAlt.Checks.T_0
public import CFSG.Certificates.Kernel.Bounds.HNAlt.Checks.W_0
public import CFSG.Certificates.Kernel.Bounds.HNAlt.Checks.W_1
public import CFSG.Certificates.Kernel.Bounds.HNAlt.Checks.X_0
import Certificates.Kernel.DceSP.Assemble

public section

#loop_join CertificateChecks.KernelBounds.HN.facts CFSG.Certificates.DSP.runFacts_append CFSG.KD.HNA.w 0 52
#loop_join CertificateChecks.KernelBounds.HN.hdr CFSG.Certificates.DSP.runHdr_append CFSG.KD.HNA.h 0 11
#loop_join CertificateChecks.KernelBounds.HN.gom CFSG.Certificates.DSP.runGom_append CFSG.KD.HNA.g 0 1
#loop_join CertificateChecks.KernelBounds.HN.os CFSG.Certificates.DSP.runSorted_append CFSG.KD.HNA.os 0 1
#loop_join CertificateChecks.KernelBounds.HN.ts CFSG.Certificates.DSP.runSorted_append CFSG.KD.HNA.ts 0 4
#loop_join CertificateChecks.KernelBounds.HN.tab CFSG.Certificates.DSP.runT_append CFSG.KD.HNA.t 0 7
#loop_join CertificateChecks.KernelBounds.HN.cover CFSG.Certificates.DSP.runCover_append CFSG.KD.HNA.c 0 21
#loop_join CertificateChecks.KernelBounds.HN.sj1 CFSG.Certificates.DSP.runStab_append CFSG.KD.HNA.s1_ 0 4
#loop_join CertificateChecks.KernelBounds.HN.ej1 CFSG.Certificates.DSP.runSorted_append CFSG.KD.HNA.es1_ 0 4
#loop_join CertificateChecks.KernelBounds.HN.sj2 CFSG.Certificates.DSP.runStab_append CFSG.KD.HNA.s2_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.ej2 CFSG.Certificates.DSP.runSorted_append CFSG.KD.HNA.es2_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.sj3 CFSG.Certificates.DSP.runStab_append CFSG.KD.HNA.s3_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.ej3 CFSG.Certificates.DSP.runSorted_append CFSG.KD.HNA.es3_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.sj4 CFSG.Certificates.DSP.runStab_append CFSG.KD.HNA.s4_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.ej4 CFSG.Certificates.DSP.runSorted_append CFSG.KD.HNA.es4_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.sj5 CFSG.Certificates.DSP.runStab_append CFSG.KD.HNA.s5_ 0 2
#loop_join CertificateChecks.KernelBounds.HN.ej5 CFSG.Certificates.DSP.runSorted_append CFSG.KD.HNA.es5_ 0 2
#loop_join CertificateChecks.KernelBounds.HN.sj6 CFSG.Certificates.DSP.runStab_append CFSG.KD.HNA.s6_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.ej6 CFSG.Certificates.DSP.runSorted_append CFSG.KD.HNA.es6_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.sj8 CFSG.Certificates.DSP.runStab_append CFSG.KD.HNA.s8_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.ej8 CFSG.Certificates.DSP.runSorted_append CFSG.KD.HNA.es8_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.sj9 CFSG.Certificates.DSP.runStab_append CFSG.KD.HNA.s9_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.ej9 CFSG.Certificates.DSP.runSorted_append CFSG.KD.HNA.es9_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.sj10 CFSG.Certificates.DSP.runStab_append CFSG.KD.HNA.s10_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.ej10 CFSG.Certificates.DSP.runSorted_append CFSG.KD.HNA.es10_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.sj11 CFSG.Certificates.DSP.runStab_append CFSG.KD.HNA.s11_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.ej11 CFSG.Certificates.DSP.runSorted_append CFSG.KD.HNA.es11_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.sj12 CFSG.Certificates.DSP.runStab_append CFSG.KD.HNA.s12_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.ej12 CFSG.Certificates.DSP.runSorted_append CFSG.KD.HNA.es12_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.sj13 CFSG.Certificates.DSP.runStab_append CFSG.KD.HNA.s13_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.ej13 CFSG.Certificates.DSP.runSorted_append CFSG.KD.HNA.es13_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.sj14 CFSG.Certificates.DSP.runStab_append CFSG.KD.HNA.s14_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.ej14 CFSG.Certificates.DSP.runSorted_append CFSG.KD.HNA.es14_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.sj15 CFSG.Certificates.DSP.runStab_append CFSG.KD.HNA.s15_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.ej15 CFSG.Certificates.DSP.runSorted_append CFSG.KD.HNA.es15_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.sj16 CFSG.Certificates.DSP.runStab_append CFSG.KD.HNA.s16_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.ej16 CFSG.Certificates.DSP.runSorted_append CFSG.KD.HNA.es16_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.sj17 CFSG.Certificates.DSP.runStab_append CFSG.KD.HNA.s17_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.ej17 CFSG.Certificates.DSP.runSorted_append CFSG.KD.HNA.es17_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.sj18 CFSG.Certificates.DSP.runStab_append CFSG.KD.HNA.s18_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.ej18 CFSG.Certificates.DSP.runSorted_append CFSG.KD.HNA.es18_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.sj19 CFSG.Certificates.DSP.runStab_append CFSG.KD.HNA.s19_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.ej19 CFSG.Certificates.DSP.runSorted_append CFSG.KD.HNA.es19_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.sj20 CFSG.Certificates.DSP.runStab_append CFSG.KD.HNA.s20_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.ej20 CFSG.Certificates.DSP.runSorted_append CFSG.KD.HNA.es20_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.sj21 CFSG.Certificates.DSP.runStab_append CFSG.KD.HNA.s21_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.ej21 CFSG.Certificates.DSP.runSorted_append CFSG.KD.HNA.es21_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.sj23 CFSG.Certificates.DSP.runStab_append CFSG.KD.HNA.s23_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.ej23 CFSG.Certificates.DSP.runSorted_append CFSG.KD.HNA.es23_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.sj24 CFSG.Certificates.DSP.runStab_append CFSG.KD.HNA.s24_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.ej24 CFSG.Certificates.DSP.runSorted_append CFSG.KD.HNA.es24_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.sj25 CFSG.Certificates.DSP.runStab_append CFSG.KD.HNA.s25_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.ej25 CFSG.Certificates.DSP.runSorted_append CFSG.KD.HNA.es25_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.sj28 CFSG.Certificates.DSP.runStab_append CFSG.KD.HNA.s28_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.ej28 CFSG.Certificates.DSP.runSorted_append CFSG.KD.HNA.es28_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.sj31 CFSG.Certificates.DSP.runStab_append CFSG.KD.HNA.s31_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.ej31 CFSG.Certificates.DSP.runSorted_append CFSG.KD.HNA.es31_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.sj32 CFSG.Certificates.DSP.runStab_append CFSG.KD.HNA.s32_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.ej32 CFSG.Certificates.DSP.runSorted_append CFSG.KD.HNA.es32_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.sj33 CFSG.Certificates.DSP.runStab_append CFSG.KD.HNA.s33_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.ej33 CFSG.Certificates.DSP.runSorted_append CFSG.KD.HNA.es33_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.sj34 CFSG.Certificates.DSP.runStab_append CFSG.KD.HNA.s34_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.ej34 CFSG.Certificates.DSP.runSorted_append CFSG.KD.HNA.es34_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.sj48 CFSG.Certificates.DSP.runStab_append CFSG.KD.HNA.s48_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.ej48 CFSG.Certificates.DSP.runSorted_append CFSG.KD.HNA.es48_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.sj49 CFSG.Certificates.DSP.runStab_append CFSG.KD.HNA.s49_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.ej49 CFSG.Certificates.DSP.runSorted_append CFSG.KD.HNA.es49_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.sj50 CFSG.Certificates.DSP.runStab_append CFSG.KD.HNA.s50_ 0 2
#loop_join CertificateChecks.KernelBounds.HN.ej50 CFSG.Certificates.DSP.runSorted_append CFSG.KD.HNA.es50_ 0 2
#loop_join CertificateChecks.KernelBounds.HN.sj51 CFSG.Certificates.DSP.runStab_append CFSG.KD.HNA.s51_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.ej51 CFSG.Certificates.DSP.runSorted_append CFSG.KD.HNA.es51_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.sj54 CFSG.Certificates.DSP.runStab_append CFSG.KD.HNA.s54_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.ej54 CFSG.Certificates.DSP.runSorted_append CFSG.KD.HNA.es54_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.sj62 CFSG.Certificates.DSP.runStab_append CFSG.KD.HNA.s62_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.ej62 CFSG.Certificates.DSP.runSorted_append CFSG.KD.HNA.es62_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.sj63 CFSG.Certificates.DSP.runStab_append CFSG.KD.HNA.s63_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.ej63 CFSG.Certificates.DSP.runSorted_append CFSG.KD.HNA.es63_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.sj64 CFSG.Certificates.DSP.runStab_append CFSG.KD.HNA.s64_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.ej64 CFSG.Certificates.DSP.runSorted_append CFSG.KD.HNA.es64_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.sj69 CFSG.Certificates.DSP.runStab_append CFSG.KD.HNA.s69_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.ej69 CFSG.Certificates.DSP.runSorted_append CFSG.KD.HNA.es69_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.sj70 CFSG.Certificates.DSP.runStab_append CFSG.KD.HNA.s70_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.ej70 CFSG.Certificates.DSP.runSorted_append CFSG.KD.HNA.es70_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.sj73 CFSG.Certificates.DSP.runStab_append CFSG.KD.HNA.s73_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.ej73 CFSG.Certificates.DSP.runSorted_append CFSG.KD.HNA.es73_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.sj75 CFSG.Certificates.DSP.runStab_append CFSG.KD.HNA.s75_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.ej75 CFSG.Certificates.DSP.runSorted_append CFSG.KD.HNA.es75_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.sj76 CFSG.Certificates.DSP.runStab_append CFSG.KD.HNA.s76_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.ej76 CFSG.Certificates.DSP.runSorted_append CFSG.KD.HNA.es76_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.sj77 CFSG.Certificates.DSP.runStab_append CFSG.KD.HNA.s77_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.ej77 CFSG.Certificates.DSP.runSorted_append CFSG.KD.HNA.es77_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.sj78 CFSG.Certificates.DSP.runStab_append CFSG.KD.HNA.s78_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.ej78 CFSG.Certificates.DSP.runSorted_append CFSG.KD.HNA.es78_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.sj79 CFSG.Certificates.DSP.runStab_append CFSG.KD.HNA.s79_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.ej79 CFSG.Certificates.DSP.runSorted_append CFSG.KD.HNA.es79_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.sj80 CFSG.Certificates.DSP.runStab_append CFSG.KD.HNA.s80_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.ej80 CFSG.Certificates.DSP.runSorted_append CFSG.KD.HNA.es80_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.sj81 CFSG.Certificates.DSP.runStab_append CFSG.KD.HNA.s81_ 0 1
#loop_join CertificateChecks.KernelBounds.HN.ej81 CFSG.Certificates.DSP.runSorted_append CFSG.KD.HNA.es81_ 0 1

#dsp_ok CertificateChecks.KernelBounds.HN.dce_ok CFSG.KD.HNA CertificateChecks.KernelBounds.HN
  CertificateChecks.KernelBounds.HN.facts CertificateChecks.KernelBounds.HN.hdr
  CertificateChecks.KernelBounds.HN.gom CertificateChecks.KernelBounds.HN.os
  CertificateChecks.KernelBounds.HN.ts CertificateChecks.KernelBounds.HN.tab
  CertificateChecks.KernelBounds.HN.cover
  [1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 23, 24, 25, 28, 31, 32,
    33, 34, 48, 49, 50, 51, 54, 62, 63, 64, 69, 70, 73, 75, 76, 77, 78, 79, 80, 81]

end
