module

public import CFSG.Certificates.Kernel.HN.PcFive
public import Certificates.Kernel.BabyMonster.PcFive.Check0
public import Certificates.Kernel.BabyMonster.PcFive.Check1
public import Certificates.Kernel.BabyMonster.PcFive.Check2
public import Certificates.Kernel.BabyMonster.PcFive.Check3
public import Certificates.Kernel.BabyMonster.PcFive.Fus
public import Certificates.Kernel.HN.PcFive.Check

public section

namespace CertificateChecks.KernelHN.PcFive

open CFSG.KC.BM.PcFive CFSG.KC.BM.PcFiveD CFSG.KC.HN.PcFive CFSG.KC.HN.PcFiveD
  CFSG.RankThree.PartOne.KS.HNFive

theorem hnFiveWitness {G : Type} [Group G] [Finite G] {k : ℕ} {q : Fin 4 → G} {z x : G}
    {r : Fin k → G} {BU : Fin k → GL (Fin 4) (ZMod 5)} {cr : Fin k → Fin 4 → ℕ} {m : ℕ}
    (hcard : Nat.card G = 5 ^ 6 * m) (hm : ¬ 5 ∣ m) (hR : Rel q z x r Mm XU cx BU cr) :
    ∀ s : G, orderOf s = 5 → CFSG.LocalAnalysis.RankFourTheoremC.RankThreeWitness 5 s := by
  have hC : ∀ k < 16, chunkOK rep 152 (1000 * k) (chunks.getD k []) = true := by
    intro k hk
    interval_cases k
    exacts [t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15]
  exact rankThreeWitness_of_rel hR tphi (elem_of_chunks hC tlen) te3 hcard hm

end CertificateChecks.KernelHN.PcFive

end
