module

public import Certificates.Kernel.Misc.Perm.HS100.CliqueGlue

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.HS100.X3

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KC.PermAdj CFSG.RankThree.Native CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.EvenSporadicStandard.HSStd.FiveY
open CertificateChecks.KernelMisc.HS100 CertificateChecks.KernelMisc.HS100.Clique
open CertificateChecks.KernelMisc.HS100.Five (eqA_F hidA pidPP)

theorem x3_orb :
    arrCertOK hsAct hsGens.size (validA 100) (keyA 100 hsKeys) x3 x3Cert = true ∧
      x3Cert.pts.size = 123200 := by
  have hN := nums'.2.1
  have h := CFSG.KC.ConjOrb.arrBfs_of_orb (ng := hsGens.size) (ngc := K3.ng) (fuel := 130000)
    (act := hsAct) (root := x3) (by rw [nums'.1]; rfl) gens_get (fun _ _ _ => rfl) K3.h hcl
    (fun i hi => K3.tr0 i (by rw [hN] at hi; omega)) (by rw [hN]; decide)
    (by rw [nums'.2.2.2.2.2, x3_eq]) x3_valid keysOK3 K3.k (by rw [hN]; norm_num)
  exact ⟨h.1, h.2.2.trans hN⟩

theorem cube_pk :
    Nat.beq (pcomp 100 7 (mask 7) X3 (pcomp 100 7 (mask 7) X3 X3)) (pidn 100 7) = true := by
  decide +kernel

theorem ne_pk : Nat.beq X3 (pidn 100 7) = false := by decide +kernel

theorem x3OK_true : x3OK = true := by
  obtain ⟨hc, hs⟩ := x3_orb
  have hc' : arrCertOKL hsAct hsGens.size (validA 100) (keyA 100 hsKeys) x3 x3Cert = true := by
    simp only [arrCertOKL, arrCertOK, Bool.and_eq_true] at hc ⊢
    obtain ⟨h1, h2⟩ := hc
    exact ⟨h1, decide_eq_true (List.isChain_iff_pairwise.2 (of_decide_eq_true h2))⟩
  have hg : allLt hsGens.size (fun k => validA 100 hsGens[k]!) = true :=
    allLt_iff.2 fun k hk => validG hk
  have hcube : eqA 100 (compA 100 x3 (compA 100 x3 x3)) (idA 100) = true := by
    rw [x3_eq, compA_unpack cX3 cX3, compA_unpack cX3 (canonK_pcomp cX3 cX3), hidA,
      eqA_F (canonK_pcomp cX3 (canonK_pcomp cX3 cX3)) pidPP.1]
    exact cube_pk
  have hne : eqA 100 x3 (idA 100) = false := by
    rw [x3_eq, hidA, eqA_F cX3 pidPP.1]
    exact ne_pk
  unfold x3OK
  rw [hg, x3_valid, hcube, hne, hc', hs]
  rfl

end CertificateChecks.KernelMisc.HS100.X3

end
