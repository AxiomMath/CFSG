module

public import Certificates.Kernel.Fi24.Chain
import Certificates.Kernel.Co2.Intro
import Certificates.Kernel.Fi24.FactsF3
import Certificates.Kernel.Fi24.FactsF4
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Fi24.Slices.Bind
import CFSG.Certificates.Kernel.Fi24.Slices.Head

public section

namespace CertificateChecks.KernelFi24

open CFSG.KC CFSG.KC.LceS CFSG.Certificates CFSG.Certificates.LCE CertificateChecks.KernelCo2

theorem s3 : Tab cg3 CFSG.KD.F3.selST (nat_lit 8) (nat_lit 18) (nat_lit 28431) :=
  lceOk_sound (lceOk_intro CFSG.KD.F3.sH1 CFSG.KD.F3.sH0 CFSG.KD.Fi24B.bHF3 CFSG.KD.F3.sH2
    CFSG.KD.F3.sH3 (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl)
    F3facts (by quickRfl) (by quickRfl) F3cover (by quickRfl)) cg3 r3

theorem s4 : Tab cg4 CFSG.KD.F4.selST (nat_lit 7) (nat_lit 16) (nat_lit 120) :=
  lceOk_sound (lceOk_intro CFSG.KD.F4.sH1 CFSG.KD.F4.sH0 CFSG.KD.Fi24B.bHF4 CFSG.KD.F4.sH2
    CFSG.KD.F4.sH3 (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl)
    F4facts (by quickRfl) (by quickRfl) F4cover (by quickRfl)) cg4 r4

theorem s5 : Tab cg5 CFSG.KD.F5.selST (nat_lit 6) (nat_lit 14) (nat_lit 56) :=
  lceOk_sound (lceOk_intro CFSG.KD.F5.sH1 CFSG.KD.F5.sH0 CFSG.KD.Fi24B.bHF5 CFSG.KD.F5.sH2
    CFSG.KD.F5.sH3 (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl)
    F5facts (by quickRfl) (by quickRfl) F5cover (by quickRfl)) cg5 r5

theorem s6 : Tab cg6 CFSG.KD.F6.selST (nat_lit 5) (nat_lit 12) (nat_lit 27) :=
  lceOk_sound (lceOk_intro CFSG.KD.F6.sH1 CFSG.KD.F6.sH0 CFSG.KD.Fi24B.bHF6 CFSG.KD.F6.sH2
    CFSG.KD.F6.sH3 (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl)
    F6facts (by quickRfl) (by quickRfl) F6cover (by quickRfl)) cg6 r6

theorem s7 : Tab cg7 CFSG.KD.F7.selST (nat_lit 4) (nat_lit 10) (nat_lit 10) :=
  lceOk_sound (lceOk_intro CFSG.KD.F7.sH1 CFSG.KD.F7.sH0 CFSG.KD.Fi24B.bHF7 CFSG.KD.F7.sH2
    CFSG.KD.F7.sH3 (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl)
    F7facts (by quickRfl) (by quickRfl) F7cover (by quickRfl)) cg7 r7

theorem s8 : Tab cg8 CFSG.KD.F8.selST (nat_lit 3) (nat_lit 8) (nat_lit 8) :=
  lceOk_sound (lceOk_intro CFSG.KD.F8.sH1 CFSG.KD.F8.sH0 CFSG.KD.Fi24B.bHF8 CFSG.KD.F8.sH2
    CFSG.KD.F8.sH3 (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl)
    F8facts (by quickRfl) (by quickRfl) F8cover (by quickRfl)) cg8 r8

theorem s9 : Tab cg9 CFSG.KD.F9.selST (nat_lit 2) (nat_lit 6) (nat_lit 4) :=
  lceOk_sound (lceOk_intro CFSG.KD.F9.sH1 CFSG.KD.F9.sH0 CFSG.KD.Fi24B.bHF9 CFSG.KD.F9.sH2
    CFSG.KD.F9.sH3 (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl)
    F9facts (by quickRfl) (by quickRfl) F9cover (by quickRfl)) cg9 r9

theorem s10 : Tab cg10 CFSG.KD.F10.selST (nat_lit 1) (nat_lit 4) (nat_lit 3) :=
  lceOk_sound (lceOk_intro CFSG.KD.F10.sH1 CFSG.KD.F10.sH0 CFSG.KD.Fi24B.bHF10 CFSG.KD.F10.sH2
    CFSG.KD.F10.sH3 (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl)
    F10facts (by quickRfl) (by quickRfl) F10cover (by quickRfl)) cg10 r10

theorem s11 : Tab cg11 CFSG.KD.F11.selST (nat_lit 0) (nat_lit 2) (nat_lit 2) :=
  lceOk_sound (lceOk_intro CFSG.KD.F11.sH1 CFSG.KD.F11.sH0 CFSG.KD.Fi24B.bHF11 CFSG.KD.F11.sH2
    CFSG.KD.F11.sH3 (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl)
    F11facts (by quickRfl) (by quickRfl) F11cover (by quickRfl)) cg11 r11

end CertificateChecks.KernelFi24

end
