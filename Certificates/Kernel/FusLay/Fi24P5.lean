module

public import Certificates.Kernel.FusLay.Fi24P5C0
public import Certificates.Kernel.FusLay.Fi24P5C1
public import Certificates.Kernel.FusLay.Fi24P5C2
public import Certificates.Kernel.FusLay.Fi24P5C3
public import Certificates.Kernel.FusLay.Fi24P5Fa
public import Certificates.Kernel.FusLay.Fi24P5Sg
public import CFSG.Certificates.Kernel.Common.ForallTree
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelFusLay.Fi24P5

open CFSG.KC.OpsLayK CFSG.RankThree.PartOne.CTP.Fus CertificateChecks.KernelFusLay.Fi24

#kc_forall_tree ch_all' (fun i => ch9586 i = true) 20 CertificateChecks.KernelFusLay.Fi24P5.ch9586
#kc_forall_tree fa_all' (fun j => fa j = true) 31 CertificateChecks.KernelFusLay.Fi24P5.fa
#kc_forall_tree seg_all (fun i => seg i = true) 6 CertificateChecks.KernelFusLay.Fi24P5.seg

theorem len : cs.length = 20 := by decide +kernel

theorem ren : renOK outs fusD2Fi24Prog cs = true := by decide +kernel

theorem ch_all : ∀ i < cs.length, ch i = true := fun i hi => ch_all' i (Nat.lt_of_lt_of_eq hi len)

theorem wB_first : Nat.beq (evalWL lay F [(fusD2Fi24.rB, 1)]) (W.WL.getD 0 lay.ONE) = true := by
  quickRfl

theorem fin_in : (fusD2Fi24.facts.all (factIn outs) && memB fusD2Fi24.rA outs &&
    memB fusD2Fi24.rB outs) = true := by decide +kernel

theorem seeds : seedRegsL lay F A B fusD2Fi24.rA fusD2Fi24.rB = true := by quickRfl

theorem ren_neg : (!renOK [0, 1, 101, 59, 72, 87, 100, 49, 109, 114, 158] fusD2Fi24Prog cs) =
    true := by decide +kernel

theorem ch_neg : (!chunkV lay (cs.getD 1 (0, [], [])) (SL.getD 2 []) (SL.getD 2 [])) = true := by
  quickRfl

theorem seg_neg : (!wsegL lay F fusD2Fi24.wB 8 0 (W.WL.getD 0 lay.ONE) (W.WL.getD 2 lay.ONE)) =
    true := by quickRfl

theorem fa_neg : (!factL lay (initR lay A B fusD2Fi24N) fusD2Fi24N
    (fusD2Fi24.facts.getD 5 default)) = true := by quickRfl

theorem seeds_neg : (!seedRegsL lay F B A fusD2Fi24.rA fusD2Fi24.rB) = true := by quickRfl

end CertificateChecks.KernelFusLay.Fi24P5

end
