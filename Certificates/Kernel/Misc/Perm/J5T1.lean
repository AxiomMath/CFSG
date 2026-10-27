module

public import Certificates.Kernel.Misc.Perm.J5K1
public import Certificates.Kernel.Misc.Perm.J5H
import CFSG.Certificates.Kernel.Spor.SiftRSound

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.J2F

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Misc.ArrEnum CFSG.KC.Misc.ChainTail
open CFSG.RankThree.PartOne CFSG.RankThree.Native CFSG.Monster.B.Co2.Native
open CFSG.KC.Misc.Clos (forall_of_chunks)
open CFSG.Monster.B.Co2 (allLt_iff)

theorem binds1 : Binds 315 9 C1.S 8 4 C1.BP (j2FiveRS 1) ((j2FiveRBase 1).map Fin.val).toArray :=
  ⟨by norm_num, by norm_num, by norm_num, Nat.eq_of_beq_eq_true rsz1,
    fun j hj => arrBind_sound (rbind1 j hj), bsz1, bget1⟩

theorem chain1 : caseChainOK3 315 (j2FiveRS 1) ((j2FiveRBase 1).map Fin.val).toArray (j2FiveRW 1)
    j2FiveGensR[0]! j2FiveGensR[1]! j2FiveGensR[2]! = true := by
  have hc := rawChainK_sound (chunks := 1) binds1 C1.head C1.hl (by norm_num) C1.hs
  have hW : j2FiveRW 1 = CFSG.Sporadic.Schreier.Co3.Native.wordsArr 3 8 j2FiveRW1 := by
    have hs : (j2FiveRS 1).size = 8 := Nat.eq_of_beq_eq_true rsz1
    rw [j2FiveRW, hs]
    rfl
  have hS : ∀ k < 3, (j2FiveRS 1)[k]! = unpack 315 9 (C1.S k) := fun k hk => binds1.2.2.2.2.1 k
    (by omega)
  have hq : ∀ k < 3, eqA 315 (unpack 315 9 (C1.S k)) (unpack 315 9 (GR k)) = true :=
    fun k hk => eqA_of (gens1 k hk).1 (gens1 k hk).2.1 (gens1 k hk).2.2
  rw [caseChainOK3, hW, hc, Bool.true_and, hS 0 (by norm_num), hS 1 (by norm_num),
    hS 2 (by norm_num), hGR 0 (by norm_num), hGR 1 (by norm_num), hGR 2 (by norm_num),
    hq 0 (by norm_num), hq 1 (by norm_num), hq 2 (by norm_num)]
  rfl

theorem cent1 : centOKP 5 315 (j2FiveRS 1) ((j2FiveRBase 1).map Fin.val).toArray (j2FiveX 1)
    (j2FiveRRels 1) (j2FiveCG 1) j2FiveKeyPts (j2FiveCCert 1) 50 = true := by
  have hbase := binds1.2.2.2.2.2
  have hbr : ∀ k < rcnt (C1.LR 0), br1 k = true := by
    rw [Nat.eq_of_beq_eq_true rc1]
    exact forall_of_chunks 63 5 _ fun c hc => by
      interval_cases c
      · exact br1_0
      · exact br1_1
      · exact br1_2
      · exact br1_3
      · exact br1_4
  have hxs : ∀ e < (CFSG.RankThree.PartOne.powPA 5 315 (j2FiveX 1)).size,
      (CFSG.RankThree.PartOne.powPA 5 315 (j2FiveX 1))[e]! = unpack 315 9 (pw (LX 1) e) := by
    rw [hLX 1 (by norm_num)]
    exact powPA_get lx1
  have hlt : ∀ r ∈ j2FiveRRels 1, r.2.2 < (CFSG.RankThree.PartOne.powPA 5 315 (j2FiveX 1)).size :=
    fun r hr => by simpa [CFSG.RankThree.PartOne.powPA] using rel_lt_of rels1 r hr
  have htail := ptailK_sound binds1 perm1 C1.hl (hLX 1 (by norm_num)) lx1 hxs hlt
    (toList_of bC1.1 bC1.2.1) pC1 (by norm_num) hbr
  simp only [centOKP, Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨?_, enumC1⟩, bC1.1⟩, ?_⟩, ?_⟩, by rw [bsz1]; exact htail⟩
  · rw [hLX 1 (by norm_num)]
    exact relsOKP_of bsz1 hbase.2 bpt1 lx1 rels1
  · rw [allLt_iff]
    intro k hk
    rw [hCG1 k hk, hLX 1 (by norm_num)]
    rw [cgs1] at hk
    exact comm_of (comm1 k hk).1 lx1 (comm1 k hk).2
  · rw [allLt_iff]
    intro k hk
    rw [hCG1 k hk]
    rw [cgs1] at hk
    exact siftK_soundR binds1 perm1 C1.hl rfl (Nat.eq_of_beq_eq_true (sift1 k hk).1)
      (sift1 k hk).2.1 (sift1 k hk).2.2

end CertificateChecks.KernelMisc.J2F

end
