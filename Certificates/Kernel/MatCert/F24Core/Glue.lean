module

public import Certificates.Kernel.MatCert.F24Core.Checks
public import CFSG.Certificates.Kernel.LocalComp.FactsVSound
public import CFSG.Blueprint.NativeSporadic
import all CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.Sporadic.Fi24Br.SeedM

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMC.F24C

open CFSG.KC.LocalComp.FactsV CFSG.AGLEmbedding.R3 CFSG.SectionRank.Native CFSG.Blueprint
open CFSG.RankThree.Asc83Table.Native
open CFSG.KD.MC.F24C (lay V P N)

theorem seedMA : CFSG.KC.LocalComp.Ops3Snd.SeedM lay (V 0) CFSG.KD.MC.F24C.LA :=
  CertificateChecks.KernelSpor.Fi24Rels.seedM_A CFSG.KD.MC.F24C.lay_ok rfl rfl
    CFSG.KD.MC.F24C.LA_eq CFSG.KD.MC.F24C.vA (by decide +kernel)

theorem seedMB : CFSG.KC.LocalComp.Ops3Snd.SeedM lay (V 1) CFSG.KD.MC.F24C.LB :=
  CertificateChecks.KernelSpor.Fi24Rels.seedM_B CFSG.KD.MC.F24C.lay_ok rfl rfl
    CFSG.KD.MC.F24C.LB_eq CFSG.KD.MC.F24C.vB (by decide +kernel)

theorem part_of {m lo hi : Nat} {Rf : Nat → Nat}
    (hr : regsV lay V P TT N CoreFi247.nregs (CoreFi247.prog.take m) Rf = true)
    (hc : ∀ i < 8, chunkV lay V P N Rf CoreFi247.nregs CoreFi247.spec.facts HH (selR lo hi) 32 i =
      true) :
    factsInRange (ops3 781) ((ops3 781).regsOf NativeSporadic.Fi24primeSeed1
      NativeSporadic.Fi24primeSeed2 CoreFi247.nregs (CoreFi247.prog.take m)) CoreFi247.nregs
      CoreFi247.spec lo hi = true :=
  facts_of_chunks (fun h f hf => factOK_of_V3S CFSG.KD.MC.F24C.lay_ok rfl rfl
    CFSG.KD.MC.F24C.LA_eq CFSG.KD.MC.F24C.LB_eq seedMA seedMB
    CFSG.KD.MC.F24C.one CFSG.KD.MC.F24C.steps hr h f hf) nfacts hc

theorem part1 : partCheckFirst (ops3 781) NativeSporadic.Fi24primeSeed1
    NativeSporadic.Fi24primeSeed2 CoreFi247.nregs CoreFi247.prog CoreFi247.spec CoreFi247.cutA
    CoreFi247.cutB = true := by
  have hf := part_of (m := 190) (lo := 0) (hi := 192) regsA_K (fun i hi => match i, hi with
    | 0, _ => chkA0 | 1, _ => chkA1 | 2, _ => chkA2 | 3, _ => chkA3 | 4, _ => chkA4
    | 5, _ => chkA5 | 6, _ => chkA6 | 7, _ => chkA7)
  have hs0 := (seed_of_V3S CFSG.KD.MC.F24C.lay_ok rfl rfl CFSG.KD.MC.F24C.LA_eq
    CFSG.KD.MC.F24C.LB_eq seedMA seedMB CFSG.KD.MC.F24C.one
    CFSG.KD.MC.F24C.steps regsA_K (r := 0) (by decide)).1 (by decide +kernel)
  have hs1 := (seed_of_V3S CFSG.KD.MC.F24C.lay_ok rfl rfl CFSG.KD.MC.F24C.LA_eq
    CFSG.KD.MC.F24C.LB_eq seedMA seedMB CFSG.KD.MC.F24C.one
    CFSG.KD.MC.F24C.steps regsA_K (r := 1) (by decide)).2 (by decide +kernel)
  unfold partCheckFirst
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, hs0⟩, hs1⟩, ?_⟩, hf⟩
  all_goals decide +kernel

theorem part2 : partCheck (ops3 781) NativeSporadic.Fi24primeSeed1 NativeSporadic.Fi24primeSeed2
    CoreFi247.nregs CoreFi247.prog CoreFi247.spec CoreFi247.cutA CoreFi247.cutB = true :=
  part_of (m := 282) (lo := 192) (hi := 284) regsB_K (fun i hi => match i, hi with
    | 0, _ => chkB0 | 1, _ => chkB1 | 2, _ => chkB2 | 3, _ => chkB3 | 4, _ => chkB4
    | 5, _ => chkB5 | 6, _ => chkB6 | 7, _ => chkB7)

theorem part3 : partCheck (ops3 781) NativeSporadic.Fi24primeSeed1 NativeSporadic.Fi24primeSeed2
    CoreFi247.nregs CoreFi247.prog CoreFi247.spec CoreFi247.cutB CoreFi247.nregs = true :=
  part_of (m := 415) (lo := 284) (hi := 417) regsC_K (fun i hi => match i, hi with
    | 0, _ => chkC0 | 1, _ => chkC1 | 2, _ => chkC2 | 3, _ => chkC3 | 4, _ => chkC4
    | 5, _ => chkC5 | 6, _ => chkC6 | 7, _ => chkC7)

end CertificateChecks.KernelMC.F24C

end
