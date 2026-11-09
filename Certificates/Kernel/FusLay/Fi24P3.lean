module

public import Certificates.Data.Kernel.OpsLayFillOne
public import CFSG.Certificates.Kernel.OpsLayChainSound
public import Certificates.Data.Kernel.OpsRenL
public import Certificates.Kernel.LocalComp.LaySnapsChunksF
public import Certificates.Kernel.FusLay.Fi24Seeds
public import CFSG.Certificates.Kernel.Common.Each
public import CFSG.Certificates.Kernel.Common.ForallTree
public import CFSG.Certificates.Kernel.F3PlanesMul
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.BetaFusFi24Inputs
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

#kc_repo #kc_json CertificateChecks.KernelFusLay.Fi24P3 "Certificates/Kernel/FusLay/data/fi24p3.json" 456 5637509512543334679
  (cs : List CFSG.KC.OpsLayK.RChunk)

#lay_snaps_chunks_f CertificateChecks.KernelFusLay.Fi24P3 3 781 CertificateChecks.KernelFusLay.Fi24.A
  CertificateChecks.KernelFusLay.Fi24.B CertificateChecks.KernelFusLay.Fi24P3.cs

namespace CertificateChecks.KernelFusLay.Fi24P3

open CFSG.KC.OpsLayK CFSG.RankThree.PartOne.CTP.Fus CertificateChecks.KernelFusLay.Fi24

@[expose] def outs : List Nat := [0, 1, 32, 36]

@[expose] noncomputable def chk (k : Nat) : Bool :=
  chunkV lay (cs.getD k (0, [], [])) (SL.getD k []) (SL.getD (k + 1) [])

@[expose] noncomputable def F : List Nat := fillR lay betaFi24P3N outs (SL.getD 16 [])

@[expose] noncomputable def fa (j : Nat) : Bool :=
  factL1 lay F betaFi24P3N (betaFi24P3.facts.getD j default)

meta def wB2 : List (Nat × Nat) := [(1, 1), (1, 1)]
meta def wY2 : List (Nat × Nat) := [(32, 1), (32, 1)]
meta def wXY : List (Nat × Nat) := [(36, 1), (32, 1)]
meta def wBY : List (Nat × Nat) := [(1, 1), (32, 1)]

end CertificateChecks.KernelFusLay.Fi24P3

#lay_wsegs_f CertificateChecks.KernelFusLay.Fi24P3.QB2 3 781 CertificateChecks.KernelFusLay.Fi24P3.S16
  CertificateChecks.KernelFusLay.Fi24P3.outs CertificateChecks.KernelFusLay.Fi24P3.wB2 2
#lay_wsegs_f CertificateChecks.KernelFusLay.Fi24P3.QY2 3 781 CertificateChecks.KernelFusLay.Fi24P3.S16
  CertificateChecks.KernelFusLay.Fi24P3.outs CertificateChecks.KernelFusLay.Fi24P3.wY2 2
#lay_wsegs_f CertificateChecks.KernelFusLay.Fi24P3.QXY 3 781 CertificateChecks.KernelFusLay.Fi24P3.S16
  CertificateChecks.KernelFusLay.Fi24P3.outs CertificateChecks.KernelFusLay.Fi24P3.wXY 2
#lay_wsegs_f CertificateChecks.KernelFusLay.Fi24P3.QBY 3 781 CertificateChecks.KernelFusLay.Fi24P3.S16
  CertificateChecks.KernelFusLay.Fi24P3.outs CertificateChecks.KernelFusLay.Fi24P3.wBY 2

namespace CertificateChecks.KernelFusLay.Fi24P3

open CFSG.KC.OpsLayK CFSG.RankThree.PartOne.CTP.Fus CertificateChecks.KernelFusLay.Fi24

#kc_each chk 0 16

@[expose] noncomputable def pX : List Nat := [getR lay F 1, getR lay F 1, getR lay F 32,
  getR lay F 32, getR lay F 36, getR lay F 32, getR lay F 1, getR lay F 32]

@[expose] noncomputable def pY : List Nat := [getR lay F 1, QB2.W0, getR lay F 32, QY2.W0,
  getR lay F 32, getR lay F 36, getR lay F 32, getR lay F 1]

@[expose] noncomputable def pZ : List Nat := [QB2.W0, lay.ONE, QY2.W0, lay.ONE, QXY.W0, QXY.W0,
  QBY.W0, QBY.W0]

@[expose] noncomputable def pr (k : Nat) : Bool :=
  mulEq lay (pX.getD k 0) (pY.getD k 0) (pZ.getD k 0)

@[expose] noncomputable def prP (k : Nat) : Bool :=
  CFSG.F3.Planes.fp3MulK lay (nat_lit 609961) (nat_lit 20) (pX.getD k 0) (pY.getD k 0) (pZ.getD k 0)

#kc_each prP 0 8

theorem fiv_pl {k : Nat} (h : prP k = true) : pr k = true :=
  CFSG.F3.Planes.fp3MulK_sound lay_ok rfl rfl (by decide) (by decide) rfl (by decide) h

theorem pr0 : pr (nat_lit 0) = true := fiv_pl prP0
theorem pr1 : pr (nat_lit 1) = true := fiv_pl prP1
theorem pr2 : pr (nat_lit 2) = true := fiv_pl prP2
theorem pr3 : pr (nat_lit 3) = true := fiv_pl prP3
theorem pr4 : pr (nat_lit 4) = true := fiv_pl prP4
theorem pr5 : pr (nat_lit 5) = true := fiv_pl prP5
theorem pr6 : pr (nat_lit 6) = true := fiv_pl prP6
theorem pr7 : pr (nat_lit 7) = true := fiv_pl prP7

#kc_each fa 0 1

theorem fa1 : fa 1 = true := factL1_ord3 (R := F) (n := betaFi24P3N) (r := 1) rfl pr0 pr1

theorem fa3 : fa 3 = true := factL1_ord3 (R := F) (n := betaFi24P3N) (r := 32) rfl pr2 pr3

theorem fa4 : fa 4 = true := factL1_comm (R := F) (n := betaFi24P3N) rfl pr4 pr5

theorem cnA : CFSG.KC.Ord.validM lay.p (lay.d * lay.S) lay.L lay.H (getR lay F 0) = true := by
  quickRfl

theorem cnY : CFSG.KC.Ord.validM lay.p (lay.d * lay.S) lay.L lay.H (getR lay F 32) = true := by quickRfl

theorem eqA12 : Nat.beq (getR lay F 0) (S12.getD 0 0) = true := by quickRfl

theorem eqY12 : Nat.beq (getR lay F 32) (S12.getD 2 0) = true := by quickRfl

theorem eqA13 : Nat.beq (getR lay F 0) (S13.getD 0 0) = true := by quickRfl

theorem eqY15 : Nat.beq (getR lay F 32) (S15.getD 2 0) = true := by quickRfl

theorem eqX16 : Nat.beq (getR lay F 36) (S16.getD 3 0) = true := by quickRfl

theorem chV : lay.mul (getR lay F 0) (getR lay F 32) = S13.getD 3 0 := by
  rw [Nat.eq_of_beq_eq_true eqA12, Nat.eq_of_beq_eq_true eqY12]
  exact chunkV_mul3_02 (c := lay) (s0 := S12.getD 0 0) (s1 := S12.getD 1 0)
    (s2 := S12.getD 2 0) (S' := S13) chk12

theorem chW : lay.mul (S13.getD 3 0) (getR lay F 0) = S14.getD 3 0 := by
  rw [Nat.eq_of_beq_eq_true eqA13]
  exact chunkV_mul4_30 (c := lay) (s0 := S13.getD 0 0) (s1 := S13.getD 1 0)
    (s2 := S13.getD 2 0) (s3 := S13.getD 3 0) (S' := S14) chk13

theorem chZ : lay.mul (S14.getD 3 0) (S14.getD 3 0) = S15.getD 3 0 :=
  chunkV_sq4_3 (c := lay) (s0 := S14.getD 0 0) (s1 := S14.getD 1 0)
    (s2 := S14.getD 2 0) (s3 := S14.getD 3 0) (S' := S15) chk14

theorem chX : lay.mul (getR lay F 32) (S15.getD 3 0) = getR lay F 36 := by
  rw [Nat.eq_of_beq_eq_true eqY15, Nat.eq_of_beq_eq_true eqX16]
  exact chunkV_mul4_23 (c := lay) (s0 := S15.getD 0 0) (s1 := S15.getD 1 0)
    (s2 := S15.getD 2 0) (s3 := S15.getD 3 0) (S' := S16) chk15

theorem chA : lay.mul (getR lay F 0) (getR lay F 0) = lay.ONE := by
  have h : factL1 lay F betaFi24P3N (.ord 0 2) = true := fa0
  simp only [factL1, Bool.and_eq_true, powK_two] at h
  exact Nat.eq_of_beq_eq_true h.2

theorem chain : lay.mul (getR lay F 36) (lay.mul (getR lay F 36) (getR lay F 36)) = lay.ONE ∧
    lay.mul (getR lay F 0) (getR lay F 36) =
      lay.mul (lay.mul (getR lay F 36) (getR lay F 36)) (getR lay F 0) :=
  chain_conj lay_ok (CFSG.KS.Ord.validM_canon lay_ok cnA) (CFSG.KS.Ord.validM_canon lay_ok cnY)
    chV chW chZ chX chA (mulEq_eq pr2) (mulEq_eq pr3) ((mulEq_eq pr4).trans (mulEq_eq pr5).symm)

theorem fa2 : fa 2 = true := factL1_ord3_eq (R := F) (n := betaFi24P3N) (r := 36) rfl chain.1

#kc_each fa 5 6

theorem fa6 : fa 6 = true := fa0

theorem fa7 : fa 7 = true := factL1_conj_eq (R := F) (n := betaFi24P3N) rfl (powK_one _ _)
  (powK_two _ _) chain.2

theorem fa8 : fa 8 = true := fa5

theorem fa9 : fa 9 = true := fa1

theorem fa10 : fa 10 = true := factL1_conj1 (R := F) (n := betaFi24P3N) rfl (powK_one _ _)
  (powK_one _ _) pr6 pr7

#kc_each fa 11 14

theorem len : cs.length = 16 := by decide +kernel

theorem ren : renOK outs betaFi24P3Prog cs = true := by decide +kernel

#kc_forall_tree ch_all' (fun i => chk i = true) 16CertificateChecks.KernelFusLay.Fi24P3.chk
#kc_forall_tree fa_all' (fun j => fa j = true) 14 CertificateChecks.KernelFusLay.Fi24P3.fa

theorem ch_all : ∀ i < cs.length, chk i = true := fun i hi => ch_all' i (Nat.lt_of_lt_of_eq hi len)

theorem fa_all : ∀ j < betaFi24P3.facts.length, fa j = true := by
  intro j hj
  have hl : betaFi24P3.facts.length = 14 := by decide +kernel
  exact fa_all' j (Nat.lt_of_lt_of_eq hj hl)

theorem fin_in : (betaFi24P3.facts.all (factIn outs) && memB betaFi24P3.rA outs &&
    memB betaFi24P3.rB outs) = true := by decide +kernel

theorem seeds : seedRegsL lay F A B betaFi24P3.rA betaFi24P3.rB = true := by quickRfl

theorem ren_neg : (!renOK [0, 1, 36, 32] betaFi24P3Prog cs) = true := by decide +kernel

@[expose] noncomputable def ng (k : Nat) : Bool :=
  [!chunkV lay (cs.getD 1 (0, [], [])) (SL.getD 1 []) (SL.getD 1 []),
    !factL1 lay (initR lay A B betaFi24P3N) betaFi24P3N (betaFi24P3.facts.getD 5 default),
    !seedRegsL lay F B A betaFi24P3.rA betaFi24P3.rB].getD k false

#kc_each ng 0 3

end CertificateChecks.KernelFusLay.Fi24P3

end
