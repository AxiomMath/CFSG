module

public import CFSG.ClassicalInvolution.SmallCases.Sporadic.J2Inputs
public import Certificates.Kernel.J2Cover.AutChains
public import Certificates.Data.Kernel.SchreierFam.J2UN
public import Certificates.Data.Kernel.SchreierFam.All3
public import Certificates.Data.Kernel.Misc.ArrEnum
public import Certificates.Data.Kernel.Spor.Prim
public import Certificates.Kernel.Sporadic.RawGen
public meta import CFSG.ClassicalInvolution.SmallCases.Sporadic.J2Inputs
public meta import Certificates.Data.Kernel.SchreierFam.J2UN
public meta import CFSG.ClassicalInvolution.SmallCases.Sporadic.J2Data
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
import Init.Data.String.Basic
import Init.Data.String.Defs
import Init.Data.ByteArray.Basic
public meta import CFSG.ClassicalInvolution.SmallCases.Sporadic.Basic
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.Basic
public meta import CFSG.ClassicalInvolution.SmallCases.Sporadic.ChainTools
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.ChainTools
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.Normalizer
public meta import CFSG.ClassicalInvolution.SmallCases.Sporadic.Normalizer
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutOddCore
public meta import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutOddCore
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public meta import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import CFSG.Sporadic.J2
public meta import CFSG.Sporadic.J2
public meta import CFSG.Sporadic.Th.F2Spec
public import CFSG.Sporadic.Th.F2Spec

set_option maxRecDepth 400000
set_option maxHeartbeats 0

#ks_rawchain CertificateChecks.KernelSchreierFam.JU 315 9 16
  CFSG.ClassicalInvolution.J2Data.uStrong CFSG.ClassicalInvolution.J2Data.uBase 4
  CFSG.KS.SchreierFam.dU

#ks_rawchain CertificateChecks.KernelSchreierFam.JN 315 9 16
  CFSG.ClassicalInvolution.J2Data.nStrong CFSG.ClassicalInvolution.J2Data.nBase 3
  CFSG.KS.SchreierFam.dN

#ks_chars CertificateChecks.KernelSchreierFam.UH CFSG.ClassicalInvolution.J2Data.uHex

#kmisc_hexflat CertificateChecks.KernelSchreierFam.UH CFSG.ClassicalInvolution.J2Data.uHex 3 315 9 4

#ks_chars CertificateChecks.KernelSchreierFam.NH CFSG.ClassicalInvolution.J2Data.nHex

#kmisc_hexflat CertificateChecks.KernelSchreierFam.NH CFSG.ClassicalInvolution.J2Data.nHex 3 315 9 4

public section

namespace CertificateChecks.KernelSchreierFam.J2

open CFSG.ClassicalInvolution.J2Data CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
  CFSG.KC.Misc.ArrEnum CFSG.KS.SchreierFam CertificateChecks.KernelJ2Cover

theorem uFS : ∀ j < 4, UH.F j = JU.S j := by decide +kernel

theorem nFS : ∀ j < 4, NH.F j = JN.S j := by decide +kernel

theorem uS : ∀ j < 4, uStrong[j]! = unpack 315 9 (JU.S j) := by
  intro j hj
  have h := CFSG.KC.Misc.HexFlat.hexTable_sound UH.all j hj
  rw [← UH.eq, uFS j hj] at h
  rw [uStrong, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
  exact h

theorem nS : ∀ j < 4, nStrong[j]! = unpack 315 9 (JN.S j) := by
  intro j hj
  have h := CFSG.KC.Misc.HexFlat.hexTable_sound NH.all j hj
  rw [← NH.eq, nFS j hj] at h
  rw [nStrong, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
  exact h

theorem uSize : Nat.beq uStrong.size 4 = true := by quickRfl

theorem nSize : Nat.beq nStrong.size 4 = true := by quickRfl

theorem nCanon : allN 3 (fun j => canonK 315 9 (mask 9) (315 * 9) (JN.S j)) = true := by quickRfl

theorem uPerm : allN 4 (fun j => permOK 315 9 (mask 9) (315 * 9) (JU.S j) (JU.SI j)) = true := by
  quickRfl

theorem nPerm : allN 4 (fun j => permOK 315 9 (mask 9) (315 * 9) (JN.S j) (JN.SI j)) = true := by
  quickRfl

theorem uBaseK : ∀ t < 1, uBase[t]! = pg 9 (mask 9) JU.BP t := by decide +kernel

theorem nBaseK : ∀ t < 2, nBase[t]! = pg 9 (mask 9) JN.BP t := by decide +kernel

theorem uOrb : (List.range 1).map (fun i => rcnt (JU.LR i)) = [32] := by decide +kernel

theorem nOrb : (List.range 2).map (fun i => rcnt (JN.LR i)) = [60, 2] := by decide +kernel

theorem uNS : 315 ≤ JU.NS * 16 := by decide +kernel

theorem nNS : 315 ≤ JN.NS * 16 := by decide +kernel

theorem canon : allN 4 (fun j => canonK 315 9 (mask 9) (315 * 9) (JU.S j)) = true ∧
    allN 2 (fun k => bAnd(canonK 315 9 (mask 9) (315 * 9) (C2A.S k),
      canonK 315 9 (mask 9) (315 * 9) (C2A.SI k))) = true := by
  constructor <;> quickRfl

theorem sA : allN 4 (fun k =>
    siftK 315 9 (mask 9) (315 * 9) (pidn 315 9) C2A.LR C2A.TRI C2A.BP 3 0 (JU.S k)) = true := by
  quickRfl

theorem sB : allN 3 (fun k =>
    siftK 315 9 (mask 9) (315 * 9) (pidn 315 9) C2B.LR C2B.TRI C2B.BP 2 0 (JN.S k)) = true := by
  quickRfl

@[expose] noncomputable def cj (k i : Nat) : Nat :=
  pcomp 315 9 (mask 9) (pcomp 315 9 (mask 9) (C2A.S k) (JU.S i)) (C2A.SI k)

theorem sC : allN 2 (fun k => allN 4 (fun i =>
    siftK 315 9 (mask 9) (315 * 9) (pidn 315 9) JU.LR JU.TRI JU.BP 1 0 (cj k i))) = true := by
  quickRfl

theorem sD : siftK 315 9 (mask 9) (315 * 9) (pidn 315 9) JN.LR JN.TRI JN.BP 2 0 (PA.S 0) = false := by
  decide +kernel

theorem dCanon : canonK 315 9 (mask 9) (315 * 9) (PA.S 0) = true := by quickRfl

@[expose] noncomputable def selfK (G : Nat) : Bool :=
  bIf(allN 4 (fun k => Nat.beq (pcomp 315 9 (mask 9) G (JU.S k)) (pcomp 315 9 (mask 9) (JU.S k) G)),
    siftK 315 9 (mask 9) (315 * 9) (pidn 315 9) JU.LR JU.TRI JU.BP 1 0 G, true)

theorem sE : all3K 315 9 (mask 9) (315 * 9) C2A.LR C2A.TR selfK = true := by quickRfl

end CertificateChecks.KernelSchreierFam.J2
