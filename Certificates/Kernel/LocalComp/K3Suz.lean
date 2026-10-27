module

public import Certificates.Kernel.LocalComp.K3SuzData
public import CFSG.Certificates.Kernel.K3Sound
public import Certificates.Kernel.LocalComp.BlockGen
public import Certificates.Kernel.LocalComp.K3SuzP0
public import Certificates.Kernel.LocalComp.K3SuzP1
public import Certificates.Kernel.LocalComp.K3SuzP2
public import Certificates.Kernel.LocalComp.K3SuzP3
public import Certificates.Kernel.LocalComp.K3SuzEP0
public import Certificates.Kernel.LocalComp.K3SuzEP1
public import Certificates.Kernel.LocalComp.K3SuzEP2
public import Certificates.Kernel.LocalComp.K3SuzEP3
public import Certificates.Kernel.LocalComp.K3SuzEP4
public import Certificates.Kernel.LocalComp.K3SuzEP5
public import Certificates.Kernel.LocalComp.K3SuzEP6
public import Certificates.Kernel.LocalComp.K3SuzEP7
public import Certificates.Kernel.LocalComp.K3SuzEP8
public import Certificates.Kernel.LocalComp.K3SuzEP9
public import Certificates.Kernel.LocalComp.K3SuzEP10
public import Certificates.Kernel.LocalComp.K3SuzEP11
public import Certificates.Kernel.LocalComp.K3SuzEP12
public import Certificates.Kernel.LocalComp.K3SuzEP13
public import Certificates.Kernel.LocalComp.K3SuzEP14
public import Certificates.Kernel.LocalComp.K3SuzEP15
public import Certificates.Kernel.LocalComp.K3SuzEP16
public import Certificates.Kernel.LocalComp.K3SuzEP17
public import Certificates.Kernel.LocalComp.K3SuzEP18
public import Certificates.Kernel.LocalComp.K3SuzEP19
public import Certificates.Kernel.LocalComp.K3SuzEP20
public import Certificates.Kernel.LocalComp.K3SuzEP21
public import Certificates.Kernel.LocalComp.K3SuzEP22
public import Certificates.Kernel.LocalComp.K3SuzEP23
public import Certificates.Kernel.LocalComp.K3SuzEP24
public import Certificates.Kernel.LocalComp.K3SuzEP25
public import Certificates.Kernel.LocalComp.K3SuzEP26
public import Certificates.Kernel.LocalComp.K3SuzEP27
public import Certificates.Kernel.LocalComp.K3SuzEP28
public import Certificates.Kernel.LocalComp.K3SuzEP29
public import Certificates.Kernel.LocalComp.K3SuzEP30
public import Certificates.Kernel.LocalComp.K3SuzEP31
public import Certificates.Kernel.LocalComp.K3SuzEP32
public import Certificates.Kernel.LocalComp.K3SuzEP33
public import Certificates.Kernel.LocalComp.K3SuzEP34
public import Certificates.Kernel.LocalComp.K3SuzEP35
public import Certificates.Kernel.LocalComp.K3SuzEP36
public import Certificates.Kernel.LocalComp.K3SuzCP0
public import Certificates.Kernel.LocalComp.K3SuzCP1
public import Certificates.Kernel.LocalComp.K3SuzCP2
public import Certificates.Kernel.LocalComp.K3SuzCP3
public import Certificates.Kernel.LocalComp.K3SuzCP4
public import Certificates.Kernel.LocalComp.K3SuzCP5
public import Certificates.Kernel.LocalComp.K3SuzCP6
public import Certificates.Kernel.LocalComp.K3SuzCP7
public import Certificates.Kernel.LocalComp.K3SuzMP0
public import Certificates.Kernel.LocalComp.K3SuzMP1
public import Certificates.Kernel.LocalComp.K3SuzMP2
public import Certificates.Kernel.LocalComp.K3SuzMP3
public import Certificates.Kernel.LocalComp.K3SuzMP4
public import Certificates.Kernel.LocalComp.K3SuzMP5
public import Certificates.Kernel.LocalComp.K3SuzMP6
public import Certificates.Kernel.LocalComp.K3SuzMP7
public import Certificates.Kernel.LocalComp.BlockJoin
public import CFSG.Certificates.Kernel.MtxKSound
meta import CFSG.Sporadic.SuzOddCore.Text
import CFSG.Certificates.Kernel.Common.Harness
import all CFSG.Sporadic.SuzOddCore.Arrays
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.Spor.RawOrbGrp

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelLC.K3.SuzM1 CFSG.Sporadic.SuzOddCore.suzP1782M1Text
#ks_chars CertificateChecks.KernelLC.K3.SuzM2 CFSG.Sporadic.SuzOddCore.suzP1782M2Text
#lc_blocks CertificateChecks.KernelLC.K3.Suz.BF CertificateChecks.KernelLC.K3.Suz.fF 74 74
#lc_blocks CertificateChecks.KernelLC.K3.Suz.BW CertificateChecks.KernelLC.K3.Suz.fW 29 1

namespace CertificateChecks.KernelLC.K3.Suz

open CFSG.KC.K3 CFSG.KC.Co3Bfs CFSG.KS.Raw CFSG.EvenSmallLie.Child3.SelK3

theorem kProg : K.progK SuzT.chars = true := by quickRfl
theorem kHead : K.headK = true := by quickRfl

theorem aS : ∀ t < 2101, fS t = true := by
  have h0 : ∀ t < 0, fS t = true := forall_lt_zero
  have h1 := cover_append (a := 0) (b := 660) h0 cS0
  have h2 := cover_append (a := 660) (b := 660) h1 cS1
  have h3 := cover_append (a := 1320) (b := 660) h2 cS2
  have h4 := cover_append (a := 1980) (b := 121) h3 cS3
  exact h4

theorem aE : ∀ t < 2187, fE t = true := by
  have h0 : ∀ t < 0, fE t = true := forall_lt_zero
  have h1 := cover_append (a := 0) (b := 60) h0 cE0
  have h2 := cover_append (a := 60) (b := 60) h1 cE1
  have h3 := cover_append (a := 120) (b := 60) h2 cE2
  have h4 := cover_append (a := 180) (b := 60) h3 cE3
  have h5 := cover_append (a := 240) (b := 60) h4 cE4
  have h6 := cover_append (a := 300) (b := 60) h5 cE5
  have h7 := cover_append (a := 360) (b := 60) h6 cE6
  have h8 := cover_append (a := 420) (b := 60) h7 cE7
  have h9 := cover_append (a := 480) (b := 60) h8 cE8
  have h10 := cover_append (a := 540) (b := 60) h9 cE9
  have h11 := cover_append (a := 600) (b := 60) h10 cE10
  have h12 := cover_append (a := 660) (b := 60) h11 cE11
  have h13 := cover_append (a := 720) (b := 60) h12 cE12
  have h14 := cover_append (a := 780) (b := 60) h13 cE13
  have h15 := cover_append (a := 840) (b := 60) h14 cE14
  have h16 := cover_append (a := 900) (b := 60) h15 cE15
  have h17 := cover_append (a := 960) (b := 60) h16 cE16
  have h18 := cover_append (a := 1020) (b := 60) h17 cE17
  have h19 := cover_append (a := 1080) (b := 60) h18 cE18
  have h20 := cover_append (a := 1140) (b := 60) h19 cE19
  have h21 := cover_append (a := 1200) (b := 60) h20 cE20
  have h22 := cover_append (a := 1260) (b := 60) h21 cE21
  have h23 := cover_append (a := 1320) (b := 60) h22 cE22
  have h24 := cover_append (a := 1380) (b := 60) h23 cE23
  have h25 := cover_append (a := 1440) (b := 60) h24 cE24
  have h26 := cover_append (a := 1500) (b := 60) h25 cE25
  have h27 := cover_append (a := 1560) (b := 60) h26 cE26
  have h28 := cover_append (a := 1620) (b := 60) h27 cE27
  have h29 := cover_append (a := 1680) (b := 60) h28 cE28
  have h30 := cover_append (a := 1740) (b := 60) h29 cE29
  have h31 := cover_append (a := 1800) (b := 60) h30 cE30
  have h32 := cover_append (a := 1860) (b := 60) h31 cE31
  have h33 := cover_append (a := 1920) (b := 60) h32 cE32
  have h34 := cover_append (a := 1980) (b := 60) h33 cE33
  have h35 := cover_append (a := 2040) (b := 60) h34 cE34
  have h36 := cover_append (a := 2100) (b := 60) h35 cE35
  have h37 := cover_append (a := 2160) (b := 27) h36 cE36
  exact h37

theorem aC : ∀ t < 445, fC t = true := by
  have h0 : ∀ t < 0, fC t = true := forall_lt_zero
  have h1 := cover_append (a := 0) (b := 60) h0 cC0
  have h2 := cover_append (a := 60) (b := 60) h1 cC1
  have h3 := cover_append (a := 120) (b := 60) h2 cC2
  have h4 := cover_append (a := 180) (b := 60) h3 cC3
  have h5 := cover_append (a := 240) (b := 60) h4 cC4
  have h6 := cover_append (a := 300) (b := 60) h5 cC5
  have h7 := cover_append (a := 360) (b := 60) h6 cC6
  have h8 := cover_append (a := 420) (b := 25) h7 cC7
  exact h8

theorem aM : ∀ t < 2187, fM t = true := by
  have h0 : ∀ t < 0, fM t = true := forall_lt_zero
  have h1 := cover_append (a := 0) (b := 300) h0 cM0
  have h2 := cover_append (a := 300) (b := 300) h1 cM1
  have h3 := cover_append (a := 600) (b := 300) h2 cM2
  have h4 := cover_append (a := 900) (b := 300) h3 cM3
  have h5 := cover_append (a := 1200) (b := 300) h4 cM4
  have h6 := cover_append (a := 1500) (b := 300) h5 cM5
  have h7 := cover_append (a := 1800) (b := 300) h6 cM6
  have h8 := cover_append (a := 2100) (b := 87) h7 cM7
  exact h8

theorem prog_eq : suzK3.prog = (List.range K.N).map (instrOf K) := by
  change parseProg suzK3Prog = _
  rw [SuzT.eq]
  exact progK_sound kProg aS

theorem gens_eq : ∀ i < K.g, suzK3.gens[i]! = tblOf K (K.GP i) := by
  intro i hi
  have hg : K.g = 2 := rfl
  rw [hg] at hi
  have h0 : CFSG.Sporadic.SuzOddCore.b0Arr = CFSG.KS.Raw.unpack K.n K.w (K.GP 0) := by
    unfold CFSG.Sporadic.SuzOddCore.b0Arr
    rw [SuzM1.eq]
    exact CFSG.KC.Mtx.mtxK_sound (by quickRfl)
  have h1 : CFSG.Sporadic.SuzOddCore.b1Arr = CFSG.KS.Raw.unpack K.n K.w (K.GP 1) := by
    unfold CFSG.Sporadic.SuzOddCore.b1Arr
    rw [SuzM2.eq]
    exact CFSG.KC.Mtx.mtxK_sound (by quickRfl)
  interval_cases i
  · rw [tblOf, ← h0]
    simp only [suzK3, List.getElem!_toArray, List.getElem!_cons_zero]
  · rw [tblOf, ← h1]
    simp only [suzK3, List.getElem!_toArray, List.getElem!_cons_succ, List.getElem!_cons_zero]

theorem check_ok : check suzK3 = true :=
  k3_sound (K := K) rfl rfl prog_eq rfl gens_eq rfl rfl rfl rfl kHead
    aS
    (cover_of_blocks (B := 74) (nb := 1) (by omega) (by decide) BF.all)
    aE
    aC
    aM
    (cover_of_blocks (B := 1) (nb := 29) (by omega) (by decide) BW.all)

end CertificateChecks.KernelLC.K3.Suz

end
