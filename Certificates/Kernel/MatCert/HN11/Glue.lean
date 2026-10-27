module

public import Certificates.Kernel.MatCert.HN11.Checks
public import Certificates.Kernel.TcGen.F5Glue
public import CFSG.Certificates.Kernel.LocalComp.FactsVSound
import all CFSG.Blueprint.NativeSporadic

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMC.HN11

open CFSG.KC.LocalComp.FactsV CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native CFSG.Blueprint
open CFSG.KD.MC.HN11 (lay V P N)

theorem lay_eq : lay = CertificateChecks.KernelTc.HN.lay := rfl

theorem v0 : V 0 = CertificateChecks.KernelTc.HN.A := by decide +kernel

theorem v1 : V 1 = CertificateChecks.KernelTc.HN.B := by decide +kernel

theorem facts : hn_11_claims.facts.all (factOK (opsP 5 133)
    ((opsP 5 133).regsOf NativeSporadic.HNSeed1 NativeSporadic.HNSeed2 hn_11_claims.nregs
      hn_11_claims.prog) hn_11_claims.nregs) = true := by
  have eA : (opsP 5 133).decode NativeSporadic.HNSeed1 = CFSG.KS.SporSch.LyM.unpackL lay.d lay.w
      lay.S (V 0) := by
    rw [v0, lay_eq]
    exact CertificateChecks.KernelTc.HN.rowsA
  have eB : (opsP 5 133).decode NativeSporadic.HNSeed2 = CFSG.KS.SporSch.LyM.unpackL lay.d lay.w
      lay.S (V 1) := by
    rw [v1, lay_eq]
    exact CertificateChecks.KernelTc.HN.rowsB
  have vA : CFSG.KC.Ord.validM lay.p (lay.d * lay.S) lay.L lay.H (V 0) = true := by
    rw [v0, lay_eq]
    exact CertificateChecks.KernelTc.HN.pay.2.2.1
  have vB : CFSG.KC.Ord.validM lay.p (lay.d * lay.S) lay.L lay.H (V 1) = true := by
    rw [v1, lay_eq]
    exact CertificateChecks.KernelTc.HN.pay.2.2.2
  have h := facts_of_chunks (fun h f hf => factOK_of_VP (p := 5) (d := 133) CFSG.KD.MC.HN11.lay_ok
      rfl rfl (by norm_num) eA eB vA vB CFSG.KD.MC.HN11.one CFSG.KD.MC.HN11.steps regs_K h f hf) nfacts
    (fun i hi => match i, hi with
      | 0, _ => chk0 | 1, _ => chk1 | 2, _ => chk2 | 3, _ => chk3 | 4, _ => chk4 | 5, _ => chk5
      | 6, _ => chk6 | 7, _ => chk7 | 8, _ => chk8 | 9, _ => chk9 | 10, _ => chk10
      | 11, _ => chk11 | 12, _ => chk12 | 13, _ => chk13)
  simpa using h

theorem sec : SClaim.check (opsP 5 133) NativeSporadic.HNSeed1 NativeSporadic.HNSeed2
    hn_11_claims = true := by
  unfold SClaim.check mcertCheck
  simp only
  rw [facts]
  decide +kernel

end CertificateChecks.KernelMC.HN11

end
