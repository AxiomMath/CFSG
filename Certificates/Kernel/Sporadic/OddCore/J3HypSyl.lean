module

public import Certificates.Kernel.Sporadic.OddCore.J3Cent
public import Certificates.Kernel.Sporadic.OddCore.MulHCmd
public import Certificates.Data.Kernel.Spor.MulHQ
public import Certificates.Data.Kernel.Spor.MulHF
public import Certificates.Data.Kernel.Spor.MulHPc
public import Certificates.Data.Kernel.Spor.PEnumC
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.J3Inputs
meta import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.J3Inputs
meta import Certificates.Data.CFSGNative.PSL3Four.Basic
meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
meta import Std.Data.HashSet
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.PcompFacts
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Rows
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public import CFSG.Walter.JRFacts
meta import CFSG.GroupTheory.Fitting.CharacteristicP
meta import CFSG.GroupTheory.LocalCores.Components
meta import CFSG.GroupTheory.LocalCores.Fitting
meta import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
meta import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
meta import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
meta import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
meta import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
meta import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
meta import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Rows
meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
meta import CFSG.Walter.JRFacts

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0

#ks_chars CertificateChecks.KernelSpor.J3HypT CFSG.EvenSporadicStandard.HypOne.J3.hypHex

#kmisc_hexflat CertificateChecks.KernelSpor.J3HypT CFSG.EvenSporadicStandard.HypOne.J3.hypHex
  4 513 13 144

namespace CertificateChecks.KernelSpor.J3HypSyl

open CFSG.EvenSporadicStandard.HypOne.J3 CFSG.Sporadic.SmallOddCore.Native CFSG.PSL3Four.Native

meta def hypM : Array (Array Nat) := (List.range 12).toArray.map fun k => natArr (hypTbl k)

meta def idM : Array Nat := idTab 6156

meta def idsM : Array (Array Nat) := Array.replicate 3 idM

meta def sM : Array (Array Nat) := sgP0.map natArr

meta def pcRecJ3 : Array (Array Nat) := (bfs (fun j t => conjTab 6156 idM sM[j]! t) 3 idM 128).tabs

meta def pcSeqJ3 (els : Array (Array Nat)) (m : Nat) : Array (Array Nat) × Array (Array Nat) :=
  Id.run do
  let idm := idTab 6156
  let mut S : Array (Array Nat) := #[idm]
  let mut set : Std.HashSet (Array Nat) := Std.HashSet.emptyWithCapacity.insert idm
  let mut ys : Array (Array Nat) := #[]
  for _ in [0:m] do
    let mut found : Option (Array Nat) := none
    for y in els do
      if found.isNone && !set.contains y && set.contains (comp 6156 y y) then
        let yi := CFSG.Monster.B.Co2.Native.invCand 6156 y
        if ys.all (fun s => set.contains (comp 6156 (comp 6156 y s) yi)) then
          found := some y
    match found with
    | some y =>
      ys := ys.push y
      let S2 := S.map fun x => comp 6156 x y
      S := S ++ S2
      set := S2.foldl (fun h x => h.insert x) set
    | none => pure ()
  return (S, ys)

meta def pcPJ3 : Array (Array Nat) × Array (Array Nat) := pcSeqJ3 pcRecJ3 7

meta def pcNJ3 : Array (Array Nat) := pcPJ3.1

meta def pcSqJ3 : Array (Array Nat) := pcPJ3.2.map fun y => comp 6156 y y

meta def pcCjJ3 : Array (Array Nat) :=
  let ys := pcPJ3.2
  ((List.range ys.size).toArray.map fun r => (List.range ys.size).toArray.map fun s =>
    if s < r then
      comp 6156 (comp 6156 ys[r]! ys[s]!) (CFSG.Monster.B.Co2.Native.invCand 6156 ys[r]!)
    else idTab 6156).flatten

meta def pcPtJ3 : Array (Array Nat) :=
  #[pcRecJ3.foldl (init := (Array.replicate 6156 0, 0)) (fun (a, j) t => (a.set! t[4]! j, j + 1)) |>.1]

end CertificateChecks.KernelSpor.J3HypSyl

#kmisc_packarrs CertificateChecks.KernelSpor.J3HypP CertificateChecks.KernelSpor.J3HypSyl.hypM 13

#kmulh CertificateChecks.KernelSpor.J3HS 6156 13 CertificateChecks.KernelSpor.J3HypSyl.idsM
  CertificateChecks.KernelSpor.J3HypSyl.sM CertificateChecks.KernelSpor.J3HypSyl.idM 128

#kfind CertificateChecks.KernelSpor.J3PcP CertificateChecks.KernelSpor.J3HypSyl.pcRecJ3
  CertificateChecks.KernelSpor.J3HypSyl.pcNJ3
#kfind CertificateChecks.KernelSpor.J3PcS CertificateChecks.KernelSpor.J3HypSyl.pcNJ3
  CertificateChecks.KernelSpor.J3HypSyl.pcRecJ3
#kfind CertificateChecks.KernelSpor.J3PcA CertificateChecks.KernelSpor.J3HypSyl.pcNJ3
  CertificateChecks.KernelSpor.J3HypSyl.pcSqJ3
#kfind CertificateChecks.KernelSpor.J3PcB CertificateChecks.KernelSpor.J3HypSyl.pcNJ3
  CertificateChecks.KernelSpor.J3HypSyl.pcCjJ3
#kfind CertificateChecks.KernelSpor.J3PcU CertificateChecks.KernelSpor.J3HypSyl.pcNJ3
  CertificateChecks.KernelSpor.J3HypSyl.sM
#kmisc_packarrs CertificateChecks.KernelSpor.J3PcPP CertificateChecks.KernelSpor.J3HypSyl.pcPtJ3 13

namespace CertificateChecks.KernelSpor.J3HypSyl

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KS.Join

theorem hyp_join : joinK 12 (13 * 513) J3HypT.F J3HypP 12 = true := by
  quickRfl

@[expose] noncomputable def cK (p : Nat) : Bool := canonK 6156 13 (mask 13) (6156 * 13) p

theorem base_ok : bAnd(szOK 6156 13, bAnd(cK (pidn 6156 13), bAnd(CFSG.KS.Prim.idK 6156 13 (mask 13),
    bAnd(cK (J3CentP 9),
    bAnd(allN 3 (fun j => bAnd(cK (J3HS.GI j), bAnd(Nat.beq (J3HS.GI j) (J3HypP (Nat.add j 1)),
      Nat.beq (J3HS.G j) (pidn 6156 13)))),
    bAnd(Nat.beq J3HS.cnt 128, penumHdK (pidn 6156 13) J3HS.cnt 128 J3HS.T J3HS.PL)))))) =
      true := by
  quickRfl

@[expose] noncomputable def ntJ3 (r k : Nat) : Bool :=
  slK (Nat.shiftLeft 1 r) (pcTK 6156 13 (mask 13) J3HS.T J3PcP r) (Nat.mul 32 k) 32

@[expose] noncomputable def rlJ3 (r c : Nat) : Bool :=
  pcRK 6156 13 (mask 13) 7 J3HS.T J3PcP J3PcA J3PcB r (Nat.mul 4 c) 4

@[expose] noncomputable def mbJ3 : Bool :=
  pcMK 6156 13 (mask 13) 3 J3HS.cnt 4 J3HS.T J3HS.GI J3PcP J3PcS J3PcU J3PcPP

@[expose] noncomputable def pcFK3 (w m k cnt p : Nat) (T G CL : Nat → Nat) (c : Nat) : Bool :=
  strictB (r32 CL c) (fun q => bAnd(Nat.blt q cnt, Nat.beq (pg w m (T q) p)
    (pg w m (T (Nat.div c k)) (pg w m (G (Nat.mod c k)) p))))

theorem ntJ3_lo : allN 5 (fun r => ntJ3 r 0) = true := by quickRfl

theorem ntJ3_5 : ntJ3 5 0 = true := by quickRfl

theorem ntJ3_60 : ntJ3 6 0 = true := by quickRfl

theorem ntJ3_61 : ntJ3 6 1 = true := by quickRfl

theorem rlJ3_lo : allN 5 (fun r => rlJ3 r 0) = true := by quickRfl

theorem rlJ3_50 : rlJ3 5 0 = true := by quickRfl

theorem rlJ3_51 : rlJ3 5 1 = true := by quickRfl

theorem rlJ3_60 : rlJ3 6 0 = true := by quickRfl

theorem rlJ3_61 : rlJ3 6 1 = true := by quickRfl

theorem mbJ3_ok : mbJ3 = true := by quickRfl

theorem clJ3 : slK (Nat.mul J3HS.cnt 3) (pcFK3 13 (mask 13) 3 J3HS.cnt 4 J3HS.T J3HS.GI J3HS.POS)
    0 384 = true := by quickRfl

theorem peJ3 : slK J3HS.cnt (CFSG.KS.PEnumC.penumPtC 3 3 J3HS.cnt J3HS.T J3HS.PL J3HS.POS J3HS.POS
    J3HS.SRT J3HS.SRI) 0 128 = true := by quickRfl

theorem sHF : slK J3HS.cnt (hsortPtKF 6156 13 (mask 13) J3HS.cnt J3HS.T J3HS.HS J3HS.HSI)
    0 J3HS.cnt = true := by quickRfl

theorem sHF_neg : hsortPtKF 6156 13 (mask 13) J3HS.cnt (fun _ => 0) J3HS.HS J3HS.HSI 0 = false := by
  decide +kernel

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 6156 13 (mask 13) p q

@[expose] noncomputable def centerK (t : Nat) : Bool :=
  (List.range 128).any (fun i => Nat.beq (J3HS.T i) t) &&
    (List.range 128).all (fun i =>
      !((List.range 3).all fun j => Nat.beq (pc (J3HS.T i) (J3HS.GI j)) (pc (J3HS.GI j) (J3HS.T i))) ||
        Nat.beq (J3HS.T i) (pidn 6156 13) || Nat.beq (J3HS.T i) t) &&
    (List.range 128).any (fun i => Nat.beq (pc (J3HS.T i) (J3HS.T i)) t)

@[expose] def j3cW : List Nat := [0, 6158, 2, 1, 2, 1, 2, 1, 1, 1, 0, 2, 1, 1, 1, 6158, 6158, 1, 1, 1,
  2, 1, 2, 1, 6158, 1, 12314, 1, 1, 1, 2, 1, 2, 1, 6158, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 2, 1, 1,
  2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6158, 1, 2, 1, 2, 1, 1, 2, 2, 1,
  1, 2, 6158, 1, 1, 6158, 2, 2, 1, 2, 2, 2, 2, 1, 2, 1, 1, 12314, 1, 2, 1, 2, 1, 1, 2, 2, 1, 1, 2,
  6158, 1, 1, 6158, 2, 2, 1, 2, 2, 2, 2, 1, 2, 2, 6158, 2, 6158]

@[expose] def j3cWJ (i : Nat) : Nat := (j3cW.getD i 0 - 1) / 6156

@[expose] def j3cWP (i : Nat) : Nat := (j3cW.getD i 0 - 1) % 6156

@[expose] noncomputable def centerWK (t i : Nat) : Bool :=
  Nat.beq (J3HS.T i) (pidn 6156 13) || Nat.beq (J3HS.T i) t ||
    (Nat.blt (j3cWJ i) 3 &&
      !Nat.beq (pg 13 (mask 13) (J3HS.T i) (pg 13 (mask 13) (J3HS.GI (j3cWJ i)) (j3cWP i)))
        (pg 13 (mask 13) (J3HS.GI (j3cWJ i)) (pg 13 (mask 13) (J3HS.T i) (j3cWP i))) &&
      Nat.blt (j3cWP i) 6156)

theorem center_wK : ((List.range 128).all (centerWK (J3CentP 9)) &&
    Nat.beq (J3HS.T 10) (J3CentP 9) && Nat.beq (pc (J3HS.T 3) (J3HS.T 3)) (J3CentP 9)) = true := by
  quickRfl

theorem center_ok : centerK (J3CentP 9) = true := by
  have h := center_wK
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hw, h1⟩, h2⟩ := h
  unfold centerK
  simp only [Bool.and_eq_true]
  refine ⟨⟨List.any_eq_true.2 ⟨10, List.mem_range.2 (by norm_num), h1⟩,
    List.all_eq_true.2 fun i hi => ?_⟩, List.any_eq_true.2 ⟨3, List.mem_range.2 (by norm_num), h2⟩⟩
  have hc := List.all_eq_true.1 hw i hi
  unfold centerWK at hc
  simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hc
  simp only [Bool.or_eq_true, Bool.not_eq_true']
  rcases hc with (h | h) | ⟨⟨hj, hne⟩, hp⟩
  · exact Or.inl (Or.inr h)
  · exact Or.inr h
  · rw [Nat.blt_eq] at hj hp
    refine Or.inl (Or.inl (List.all_eq_false.2 ⟨j3cWJ i, List.mem_range.2 hj, fun he => ?_⟩))
    have hx := congrArg (fun q => pg 13 (mask 13) q (j3cWP i)) (Nat.eq_of_beq_eq_true he)
    simp only [pc] at hx
    rw [PF.pg_pcomp (n := 6156) (by norm_num) hp, PF.pg_pcomp (n := 6156) (by norm_num) hp] at hx
    exact Nat.ne_of_beq_eq_false hne hx

end CertificateChecks.KernelSpor.J3HypSyl

end
