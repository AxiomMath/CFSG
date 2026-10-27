module

public import Certificates.Kernel.LocalComp.Co1FusData
public import Certificates.Kernel.LocalComp.M1Gen
public import CFSG.Certificates.Kernel.LocalCompCo1FusSound
public import CFSG.LocalAnalysis.ComponentClassification.AS81Step18Co1Tests
meta import Certificates.Data.CFSGNative.Co1.Data
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.Co1Block.TwoCCheckInputs

public section

set_option maxRecDepth 400000
set_option exponentiation.threshold 600

#ks_chars CertificateChecks.KernelLC.Co1Fus.SA CFSG.Sporadic.Co1.Native.seedA
#ks_chars CertificateChecks.KernelLC.Co1Fus.SB CFSG.Sporadic.Co1.Native.seedB
#lc_m1 CertificateChecks.KernelLC.Co1Fus.SA CFSG.Sporadic.Co1.Native.seedA 24
#lc_m1 CertificateChecks.KernelLC.Co1Fus.SB CFSG.Sporadic.Co1.Native.seedB 24

namespace CertificateChecks.KernelLC.Co1Fus

open CFSG.KC.F2Dag CFSG.KC.M1F2 CFSG.Sporadic.Co1Schreier.Native
open CFSG.ComponentClassification.AS81.Co1Fusion CFSG.Sporadic.Co1Block
open CFSG.Sporadic.SmallF2.Native

theorem kSeeds : (Nat.beq SA.M PA && Nat.beq SB.M PB) = true := by quickRfl

theorem kInvA : (canonF 24 PA && canonF 24 PAI && Nat.beq (mulF 24 PA PAI) (idF 24)) = true := by
  quickRfl

theorem kInvB : (canonF 24 PB && canonF 24 PBI && Nat.beq (mulF 24 PB PBI) (idF 24)) = true := by
  quickRfl

theorem kH0 : Nat.beq (wordK 24 [PA, PB] [PAI, PBI] 2
    (CFSG.Sporadic.Co1Schreier.Data.stabWord0.map Int.ofNat)) PH0 = true := by
  quickRfl

theorem kH1 : Nat.beq (wordK 24 [PA, PB] [PAI, PBI] 2
    (CFSG.Sporadic.Co1Schreier.Data.stabWord1.map Int.ofNat)) PH1 = true := by
  quickRfl

theorem kIota : dagK 24 2 iotaDerivs IE IEI = true := by quickRfl

theorem k13 : dagK 24 3 (twoBD1 ++ fus13Words) E13 EI13 = true := by quickRfl

theorem k13f : fusK 24 PA E13 44 46 13 3 = true := by quickRfl

theorem k11 : dagK 24 3 (twoCD1 ++ fus11Words) E11 EI11 = true := by quickRfl

theorem k11f : fusK 24 (IE.getD 51 (idF 24)) E11 36 38 11 1 = true := by quickRfl

theorem kIotaBase : IE.take 2 = [PH0, PH1] := rfl

theorem k13b : E13.take 3 = [PA, PB, PA] := rfl

theorem k11b : E11.take 3 = [PA, PB, IE.getD 51 (idF 24)] := rfl

theorem aR_eq : aR = unpackF 24 PA := by
  have h := rowsOfPayload_unpack SA.bind
  rw [← SA.eq] at h
  have e : SA.M = PA := by
    have := kSeeds
    rw [Bool.and_eq_true] at this
    exact Nat.eq_of_beq_eq_true this.1
  rw [e] at h
  exact h

theorem bR_eq : bR = unpackF 24 PB := by
  have h := rowsOfPayload_unpack SB.bind
  rw [← SB.eq] at h
  have e : SB.M = PB := by
    have := kSeeds
    rw [Bool.and_eq_true] at this
    exact Nat.eq_of_beq_eq_true this.2
  rw [e] at h
  exact h

theorem invA_eq : inv aR = unpackF 24 PAI := by
  have h := kInvA
  simp only [Bool.and_eq_true] at h
  rw [aR_eq]
  exact inv_unpack (canon_lt h.1.1) (canon_lt h.1.2) h.2

theorem invB_eq : inv bR = unpackF 24 PBI := by
  have h := kInvB
  simp only [Bool.and_eq_true] at h
  rw [bR_eq]
  exact inv_unpack (canon_lt h.1.1) (canon_lt h.1.2) h.2

theorem hRows0_eq : hRows0 = unpackF 24 PH0 := by
  unfold hRows0
  rw [invA_eq, invB_eq, aR_eq, bR_eq]
  have h := word_unpack [PA, PB] [PAI, PBI] rfl
    (CFSG.Sporadic.Co1Schreier.Data.stabWord0.map Int.ofNat)
  simp only [List.map_cons, List.map_nil] at h
  rw [h]
  exact congrArg (unpackF 24) (Nat.eq_of_beq_eq_true kH0)

theorem hRows1_eq : hRows1 = unpackF 24 PH1 := by
  unfold hRows1
  rw [invA_eq, invB_eq, aR_eq, bR_eq]
  have h := word_unpack [PA, PB] [PAI, PBI] rfl
    (CFSG.Sporadic.Co1Schreier.Data.stabWord1.map Int.ofNat)
  simp only [List.map_cons, List.map_nil] at h
  rw [h]
  exact congrArg (unpackF 24) (Nat.eq_of_beq_eq_true kH1)

theorem iotaC_eq : iotaCRows = unpackF 24 (IE.getD 51 (idF 24)) := by
  unfold iotaCRows iotaRows
  rw [hRows0_eq, hRows1_eq]
  have h := dagK_sound kIota
  rw [kIotaBase] at h
  simp only [List.map_cons, List.map_nil] at h
  rw [h, one_unpack, List.getD_map]

theorem fus13 : fus13Check = true := fusCheckOf_of_K aR_eq bR_eq aR_eq k13b k13 k13f

theorem fus11 : fus11Check = true := fusCheckOf_of_K aR_eq bR_eq iotaC_eq k11b k11 k11f

open Certificates in
open CFSG in
theorem cert15071 : CFSG.ComponentClassification.AS81.Co1Fusion.fus13Check = true ∧
    CFSG.ComponentClassification.AS81.Co1Fusion.fus11Check = true := ⟨fus13, fus11⟩

end CertificateChecks.KernelLC.Co1Fus

end
