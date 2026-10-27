module

public import Certificates.Kernel.SporSch.HN.C17381Data
public import Certificates.Kernel.SporSch.HN.Pt2109Data
public import Certificates.Kernel.SporSch.HN.PtR
public import Certificates.Data.Kernel.SporSch.ConjKey
public import Certificates.Data.Kernel.SporSch.HNXOrb
public import Certificates.Data.Kernel.SporSch.HNXPrim
public import Certificates.Data.Kernel.SporSch.HNXPt
public import CFSG.Certificates.Kernel.Local.HN.Lib
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.HN17381

open CFSG.KC.ConjKey CFSG.KC.LL CFSG.KS.SporSch CFSG.HardMathSupport.Dickson.I271.HNFive.Native

local notation "mm" => CFSG.KC.LL.HN.mm
local notation "sI" => CFSG.KC.LL.HN.subI
local notation "ONE" => CFSG.KD.OrdHN.ONE
local notation "G" => CFSG.KD.HNPt2109.C3_6
local notation "KGI" => CFSG.KD.HN17381.GI
local notation "KY" => CFSG.KD.HN17381.Y
local notation "KS" => CFSG.KD.HN17381.S
local notation "KC" => CFSG.KD.HN17381.C
local notation "KQ" => CFSG.KD.HN17381.Q
local notation "KA" => CFSG.KD.HN17381.A
local notation "KL" => CFSG.KD.HN17381.LAM
local notation "KR" => CFSG.KD.HN17381.RR
local notation "KW" => CFSG.KD.HN17381.WW
local notation "KF" => CFSG.KD.HN17381.PHI

@[expose] noncomputable def addL (X Y : Nat) : Nat :=
  CFSG.KC.Ord.redP (nat_lit 13) CFSG.KD.OrdHN.L CFSG.KD.OrdHN.H (nat_lit 5) (nat_lit 9) (Nat.add X Y)

@[expose] noncomputable def e0 (X j : Nat) : Nat := fldW X (Nat.mul (nat_lit 13) j) (nat_lit 13)

theorem ch17381_pow : eqK (mm (mm (mm (mm (mm G G) G) G) G) G) KY = true ∧
    eqK (mm (mm (mm (mm KY G) G) G) G) KS = true ∧ eqK (mm (mm KS KS) KS) ONE = true ∧
    eqK (mm G KGI) ONE = true ∧ validHN KGI = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> quickRfl

theorem ch17381_c : eqK (HNX.wordC CFSG.KD.HNPt.R (cWord.map (33 + ·))) KC = true := by quickRfl

theorem ch17381_q : eqK (mm (mm (mm (mm KGI KC) G) KC) KGI) KQ = true := by quickRfl

theorem ch17381_ent : Bool.not (Nat.beq (e0 KY 1) 0) = true ∧ Bool.not (Nat.beq (e0 KS 0) 1) = true ∧
    Bool.not (Nat.beq (e0 (mm KS KQ) 0) (e0 (mm KQ KS) 0)) = true := by
  refine ⟨?_, ?_, ?_⟩ <;> quickRfl

theorem ch17381_qy : eqK (mm KQ KY) (mm KY KQ) = true := by quickRfl

theorem ch17381_ker : eqK (mm (sI KY) KA) 0 = true ∧
    eqK (addL (mm KA KL) (mm KR (sI KY))) ONE = true ∧
    eqK (mm (sI KQ) KA) (mm (mm (sI KY) (sI KY)) KW) = true ∧
    eqK (mm KF (mm (sI KY) (sI KY))) 0 = true ∧
    Bool.not (Nat.beq (e0 (mm (mm KF (sI KS)) KA) 1) 0) = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> quickRfl

theorem ch17381_pay : seedRK KA CFSG.KD.HN17381.pA.chars = true ∧
    seedRK KL CFSG.KD.HN17381.pL.chars = true ∧ seedRK KR CFSG.KD.HN17381.pR.chars = true ∧
    seedRK KW CFSG.KD.HN17381.pW.chars = true ∧ seedRK KF CFSG.KD.HN17381.pF.chars = true ∧
    validHN KA = true ∧ validHN KL = true ∧ validHN KR = true ∧ validHN KW = true ∧
    validHN KF = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> quickRfl

end CertificateChecks.KernelSporSch.HN17381

end
