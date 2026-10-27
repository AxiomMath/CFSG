module

public import Certificates.Kernel.Sporadic.OddCore.SuzOutV0
public import Certificates.Kernel.Sporadic.OddCore.SuzK0C
public import Certificates.Kernel.Sporadic.OddCore.SuzK0S0
public import Certificates.Kernel.Sporadic.OddCore.SuzK0S1
public import Certificates.Kernel.Sporadic.OddCore.SuzK0S2
public import Certificates.Kernel.Sporadic.OddCore.SuzK0S3
public import Certificates.Kernel.Sporadic.OddCore.SuzK0S4
public import Certificates.Kernel.Sporadic.OddCore.SuzK0S5
public import Certificates.Kernel.Sporadic.OddCore.SuzK0S6
public import Certificates.Kernel.Sporadic.OddCore.SuzK0S7
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue
import Certificates.Kernel.Sporadic.ON.Gen
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

set_option maxRecDepth 400000

#kon_join CertificateChecks.KernelSpor.SuzK0.kAll CertificateChecks.KernelSpor.SuzK0.kSl 32

namespace CertificateChecks.KernelSpor.SuzK0

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KC.BfsPin
open CFSG.KC.L34K CFSG.KC.L34Scan CFSG.KC.CentScan
open CFSG.Sporadic.SuzOddCore CFSG.PSL3Four.Native CFSG.EvenSporadicStandard.Solomon78
open CertificateChecks.KernelSpor

theorem hd_parts : SK0.cnt = 40320 ∧ SK0.k = 22 ∧
    penumHdK (pidn 42 6) SK0.cnt 40320 SK0.T SK0.PL = true ∧
    ∀ j < 22, SK0.G j = SuzDK.K j := by
  obtain ⟨h1, h⟩ := andT k_hd
  obtain ⟨h2, h⟩ := andT h
  obtain ⟨h3, h4⟩ := andT h
  exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, h3,
    fun j hj => Nat.eq_of_beq_eq_true (CFSG.KS.Raw.Orb.allN_iff.1 h4 j hj)⟩

theorem gens_ok : GensOK 42 6 22 SK0.G (kGens 0) := by
  refine ⟨SuzD.kGens_size, fun j hj => ?_⟩
  rw [hd_parts.2.2.2 j hj]
  exact ⟨SuzD.kGens_get hj, (SuzD.kparts hj).1⟩

theorem pt_ok {i : Nat} (hi : i < SK0.cnt) :
    penumPtK 42 6 (mask 6) (42 * 6) false SK0.G SK0.GI 22 SK0.cnt SK0.T SK0.PL SK0.POS SK0.SRT
      SK0.SRI i = true := by
  have hc : SK0.cnt = 40320 := hd_parts.1
  have hs : i / 1260 < 32 := by omega
  have h := kAll (i / 1260) hs
  unfold kSl at h
  refine penumSl_spec h i ?_ ?_ hi
  · change i / 1260 * 1260 ≤ i
    omega
  · change i < i / 1260 * 1260 + 1260
    omega

theorem pt_canon {i : Nat} (hi : i < SK0.cnt) : canonK 42 6 (mask 6) (42 * 6) (SK0.T i) = true :=
  penumPt_canon (pt_ok hi)

theorem enum_eq : enumOf 42 (kGens 0) 40320 = penumRec 42 6 SK0.cnt SK0.T SK0.PL := by
  unfold enumOf
  exact (penumK_left_sound (cap := 40320) hsz42 gens_ok hd_parts.2.2.1 fun _ hi => pt_ok hi).1

theorem penumRec_tabs (n w cnt : Nat) (T PL : Nat → Nat) :
    (penumRec n w cnt T PL).tabs = pts n w cnt T :=
  rfl

theorem tabs_eq : suzRangeTabs = pts 42 6 SK0.cnt SK0.T := by
  unfold suzRangeTabs
  rw [enum_eq, penumRec_tabs]

theorem scan {i : Nat} (hi : i < SK0.cnt) :
    centIdK 42 6 5 SuzDP (pidn 42 6) (SK0.T i) = true ∧
      offK 42 6 5 SuzDP (SuzSV 0) (SK0.T i) = true := by
  have hN : SK0.cnt = 1260 * 32 := by rw [hd_parts.1]
  have h := scanSl_spec (f := fun x => CFSG.KLie.CT.andB (centIdK 42 6 5 SuzDP (pidn 42 6) x)
    (offK 42 6 5 SuzDP (SuzSV 0) x)) hN (by decide) (fun s hs => by
      have h1 := scAll s hs
      unfold scSl at h1
      rwa [strictB_app, strictB_app] at h1) i hi
  exact andT h

theorem check26681 : suzOuterCheck = true := by
  have hg := SuzOut.dGens_size
  have hgs : ∀ c < 5, dGens[c]! = unpack 42 6 (SuzDP c) := fun c hc => (SuzOut.dp_get hc).1
  have hc : ∀ c < 5, canonK 42 6 (mask 6) (42 * 6) (SuzDP c) = true :=
    fun c hc => (SuzOut.dp_get hc).2
  unfold suzOuterCheck suzCentCheck suzCosetCheck
  rw [SuzOut.relOK, tabs_eq, SuzOut.sv_eq,
    centralOK_of hsz42 (fun _ hi => pt_canon hi) hg hgs hc (fun _ hi => (scan hi).1),
    offOK_of (fun _ hi => pt_canon hi) SuzOut.sv_parts.2.1 hg hgs hc (fun _ hi => (scan hi).2)]
  rfl

end CertificateChecks.KernelSpor.SuzK0

end
