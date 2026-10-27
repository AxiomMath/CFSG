module

public import Certificates.Kernel.Misc.Perm.J5K5
public import Certificates.Kernel.Misc.Perm.J5H
import CFSG.Certificates.Kernel.Spor.SiftRSound

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.J2F

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Misc.ArrEnum CFSG.KC.Misc.ChainTail
open CFSG.RankThree.PartOne CFSG.RankThree.Native CFSG.Monster.B.Co2.Native
open CFSG.KC.Misc.Clos (forall_of_chunks)
open CFSG.Monster.B.Co2 (allLt_iff)

theorem binds5 : Binds 315 9 C5.S 8 4 C5.BP (j2FiveRS 5) ((j2FiveRBase 5).map Fin.val).toArray :=
  ⟨by norm_num, by norm_num, by norm_num, Nat.eq_of_beq_eq_true rsz5,
    fun j hj => arrBind_sound (rbind5 j hj), bsz5, bget5⟩

theorem chain5 : caseChainOK3 315 (j2FiveRS 5) ((j2FiveRBase 5).map Fin.val).toArray (j2FiveRW 5)
    j2FiveGensR[0]! j2FiveGensR[1]! j2FiveGensR[2]! = true := by
  have hc := rawChainK_sound (chunks := 1) binds5 C5.head C5.hl (by norm_num) C5.hs
  have hW : j2FiveRW 5 = CFSG.Sporadic.Schreier.Co3.Native.wordsArr 3 8 j2FiveRW5 := by
    have hs : (j2FiveRS 5).size = 8 := Nat.eq_of_beq_eq_true rsz5
    rw [j2FiveRW, hs]
    rfl
  have hS : ∀ k < 3, (j2FiveRS 5)[k]! = unpack 315 9 (C5.S k) := fun k hk => binds5.2.2.2.2.1 k
    (by omega)
  have hq : ∀ k < 3, eqA 315 (unpack 315 9 (C5.S k)) (unpack 315 9 (GR k)) = true :=
    fun k hk => eqA_of (gens5 k hk).1 (gens5 k hk).2.1 (gens5 k hk).2.2
  rw [caseChainOK3, hW, hc, Bool.true_and, hS 0 (by norm_num), hS 1 (by norm_num),
    hS 2 (by norm_num), hGR 0 (by norm_num), hGR 1 (by norm_num), hGR 2 (by norm_num),
    hq 0 (by norm_num), hq 1 (by norm_num), hq 2 (by norm_num)]
  rfl

theorem cent5 : centOKP 5 315 (j2FiveRS 5) ((j2FiveRBase 5).map Fin.val).toArray (j2FiveX 5)
    (j2FiveRRels 5) (j2FiveCG 5) j2FiveKeyPts (j2FiveCCert 5) 300 = true := by
  have hbase := binds5.2.2.2.2.2
  have hbr : ∀ k < rcnt (C5.LR 0), br5 k = true := by
    rw [Nat.eq_of_beq_eq_true rc5]
    exact forall_of_chunks 63 5 _ fun c hc => by
      interval_cases c
      · exact br5_0
      · exact br5_1
      · exact br5_2
      · exact br5_3
      · exact br5_4
  have hxs : ∀ e < (CFSG.RankThree.PartOne.powPA 5 315 (j2FiveX 5)).size,
      (CFSG.RankThree.PartOne.powPA 5 315 (j2FiveX 5))[e]! = unpack 315 9 (pw (LX 5) e) := by
    rw [hLX 5 (by norm_num)]
    exact powPA_get lx5
  have hlt : ∀ r ∈ j2FiveRRels 5, r.2.2 < (CFSG.RankThree.PartOne.powPA 5 315 (j2FiveX 5)).size :=
    fun r hr => by simpa [CFSG.RankThree.PartOne.powPA] using rel_lt_of rels5 r hr
  have htail := ptailK_sound binds5 perm5 C5.hl (hLX 5 (by norm_num)) lx5 hxs hlt
    (toList_of bC5.1 bC5.2.1) pC5 (by norm_num) hbr
  simp only [centOKP, Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨?_, enumC5⟩, bC5.1⟩, ?_⟩, ?_⟩, by rw [bsz5]; exact htail⟩
  · rw [hLX 5 (by norm_num)]
    exact relsOKP_of bsz5 hbase.2 bpt5 lx5 rels5
  · rw [allLt_iff]
    intro k hk
    rw [hCG5 k hk, hLX 5 (by norm_num)]
    rw [cgs5] at hk
    exact comm_of (comm5 k hk).1 lx5 (comm5 k hk).2
  · rw [allLt_iff]
    intro k hk
    rw [hCG5 k hk]
    rw [cgs5] at hk
    exact siftK_soundR binds5 perm5 C5.hl rfl (Nat.eq_of_beq_eq_true (sift5 k hk).1)
      (sift5 k hk).2.1 (sift5 k hk).2.2

end CertificateChecks.KernelMisc.J2F

end
