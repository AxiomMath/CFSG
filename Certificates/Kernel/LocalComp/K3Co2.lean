module

public import Certificates.Kernel.LocalComp.K3Co2Data
public import CFSG.Certificates.Kernel.K3Sound
public import Certificates.Kernel.LocalComp.BlockGen
public import Certificates.Kernel.LocalComp.K3Co2P0
public import Certificates.Kernel.LocalComp.K3Co2P1
public import Certificates.Kernel.LocalComp.K3Co2P2
public import Certificates.Kernel.LocalComp.K3Co2P3
public import Certificates.Kernel.LocalComp.K3Co2P4
public import Certificates.Kernel.LocalComp.K3Co2EP0
public import Certificates.Kernel.LocalComp.K3Co2EP1
public import Certificates.Kernel.LocalComp.K3Co2EP2
public import Certificates.Kernel.LocalComp.K3Co2EP3
public import Certificates.Kernel.LocalComp.K3Co2EP4
public import Certificates.Kernel.LocalComp.K3Co2EP5
public import Certificates.Kernel.LocalComp.K3Co2EP6
public import Certificates.Kernel.LocalComp.K3Co2EP7
public import Certificates.Kernel.LocalComp.K3Co2EP8
public import Certificates.Kernel.LocalComp.K3Co2EP9
public import Certificates.Kernel.LocalComp.K3Co2EP10
public import Certificates.Kernel.LocalComp.K3Co2EP11
public import Certificates.Kernel.LocalComp.K3Co2EP12
public import Certificates.Kernel.LocalComp.K3Co2CP0
public import Certificates.Kernel.LocalComp.K3Co2CP1
public import Certificates.Kernel.LocalComp.K3Co2CP2
public import Certificates.Kernel.LocalComp.K3Co2MP0
public import Certificates.Kernel.LocalComp.K3Co2MP1
public import Certificates.Kernel.LocalComp.K3Co2MP2
public import Certificates.Kernel.LocalComp.K3Co2MP3
public import Certificates.Kernel.LocalComp.BlockJoin
public import CFSG.Certificates.Kernel.LBindSound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.Spor.RawOrbGrp

public section

set_option maxRecDepth 400000

#lc_blocks CertificateChecks.KernelLC.K3.Co2.BF CertificateChecks.KernelLC.K3.Co2.fF 74 74
#lc_blocks CertificateChecks.KernelLC.K3.Co2.BW CertificateChecks.KernelLC.K3.Co2.fW 20 1

namespace CertificateChecks.KernelLC.K3.Co2

open CFSG.KC.K3 CFSG.KC.Co3Bfs CFSG.KS.Raw CFSG.EvenSmallLie.Child3.SelK3

theorem kProg : K.progK Co2T.chars = true := by quickRfl
theorem kHead : K.headK = true := by quickRfl

theorem aS : ∀ t < 2284, fS t = true := by
  have h0 : ∀ t < 0, fS t = true := forall_lt_zero
  have h1 := cover_append (a := 0) (b := 480) h0 cS0
  have h2 := cover_append (a := 480) (b := 480) h1 cS1
  have h3 := cover_append (a := 960) (b := 480) h2 cS2
  have h4 := cover_append (a := 1440) (b := 480) h3 cS3
  have h5 := cover_append (a := 1920) (b := 364) h4 cS4
  exact h5

theorem aE : ∀ t < 729, fE t = true := by
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
  have h13 := cover_append (a := 720) (b := 9) h12 cE12
  exact h13

theorem aC : ∀ t < 148, fC t = true := by
  have h0 : ∀ t < 0, fC t = true := forall_lt_zero
  have h1 := cover_append (a := 0) (b := 60) h0 cC0
  have h2 := cover_append (a := 60) (b := 60) h1 cC1
  have h3 := cover_append (a := 120) (b := 28) h2 cC2
  exact h3

theorem aM : ∀ t < 729, fM t = true := by
  have h0 : ∀ t < 0, fM t = true := forall_lt_zero
  have h1 := cover_append (a := 0) (b := 240) h0 cM0
  have h2 := cover_append (a := 240) (b := 240) h1 cM1
  have h3 := cover_append (a := 480) (b := 240) h2 cM2
  have h4 := cover_append (a := 720) (b := 9) h3 cM3
  exact h4

theorem prog_eq : co2K3.prog = (List.range K.N).map (instrOf K) := by
  change parseProg co2K3Prog = _
  rw [Co2T.eq]
  exact progK_sound kProg aS

theorem gens_eq : ∀ i < K.g, co2K3.gens[i]! = tblOf K (K.GP i) := by
  intro i hi
  have hg : K.g = 2 := rfl
  rw [hg] at hi
  have e0 : CFSG.Sporadic.Co2Cert.co2OrigArrs[0]! = CFSG.Sporadic.Co2Cert.co2G0.toArray := by
    simp only [CFSG.Sporadic.Co2Cert.co2OrigArrs, CFSG.Sporadic.Co2Cert.co2Rec, Function.const,
      CFSG.Sporadic.Co2Cert.co2RecLit, CFSG.Sporadic.Co2Cert.co2Chain,
      CFSG.Monster.B.Mathieu.ChainRecord.origArrs, List.map_cons, List.map_nil,
      List.getElem!_toArray, List.getElem!_cons_zero]
  have e1 : CFSG.Sporadic.Co2Cert.co2OrigArrs[1]! = CFSG.Sporadic.Co2Cert.co2G1.toArray := by
    simp only [CFSG.Sporadic.Co2Cert.co2OrigArrs, CFSG.Sporadic.Co2Cert.co2Rec, Function.const,
      CFSG.Sporadic.Co2Cert.co2RecLit, CFSG.Sporadic.Co2Cert.co2Chain,
      CFSG.Monster.B.Mathieu.ChainRecord.origArrs, List.map_cons, List.map_nil,
      List.getElem!_toArray, List.getElem!_cons_succ, List.getElem!_cons_zero]
  have h0 : CFSG.Sporadic.Co2Cert.co2OrigArrs[0]! = CFSG.KS.Raw.unpack K.n K.w (K.GP 0) := by
    rw [e0]
    exact CFSG.KS.Raw.lbindK_sound (by quickRfl)
  have h1 : CFSG.Sporadic.Co2Cert.co2OrigArrs[1]! = CFSG.KS.Raw.unpack K.n K.w (K.GP 1) := by
    rw [e1]
    exact CFSG.KS.Raw.lbindK_sound (by quickRfl)
  interval_cases i
  · rw [tblOf, ← h0]
    simp only [co2K3, List.getElem!_toArray, List.getElem!_cons_zero]
  · rw [tblOf, ← h1]
    simp only [co2K3, List.getElem!_toArray, List.getElem!_cons_succ, List.getElem!_cons_zero]

theorem check_ok : check co2K3 = true :=
  k3_sound (K := K) rfl rfl prog_eq rfl gens_eq rfl rfl rfl rfl kHead
    aS
    (cover_of_blocks (B := 74) (nb := 1) (by omega) (by decide) BF.all)
    aE
    aC
    aM
    (cover_of_blocks (B := 1) (nb := 20) (by omega) (by decide) BW.all)

end CertificateChecks.KernelLC.K3.Co2

end
