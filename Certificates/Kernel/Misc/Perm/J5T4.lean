module

public import Certificates.Kernel.Misc.Perm.J5K4
public import Certificates.Kernel.Misc.Perm.J5H
import CFSG.Certificates.Kernel.Spor.SiftRSound

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.J2F

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Misc.ArrEnum CFSG.KC.Misc.ChainTail
open CFSG.RankThree.PartOne CFSG.RankThree.Native CFSG.Monster.B.Co2.Native
open CFSG.KC.Misc.Clos (forall_of_chunks)
open CFSG.Monster.B.Co2 (allLt_iff)

theorem binds4 : Binds 315 9 C4.S 7 4 C4.BP (j2FiveRS 4) ((j2FiveRBase 4).map Fin.val).toArray :=
  ⟨by norm_num, by norm_num, by norm_num, Nat.eq_of_beq_eq_true rsz4,
    fun j hj => arrBind_sound (rbind4 j hj), bsz4, bget4⟩

theorem chain4 : caseChainOK3 315 (j2FiveRS 4) ((j2FiveRBase 4).map Fin.val).toArray (j2FiveRW 4)
    j2FiveGensR[0]! j2FiveGensR[1]! j2FiveGensR[2]! = true := by
  have hc := rawChainK_sound (chunks := 1) binds4 C4.head C4.hl (by norm_num) C4.hs
  have hW : j2FiveRW 4 = CFSG.Sporadic.Schreier.Co3.Native.wordsArr 3 7 j2FiveRW4 := by
    have hs : (j2FiveRS 4).size = 7 := Nat.eq_of_beq_eq_true rsz4
    rw [j2FiveRW, hs]
    rfl
  have hS : ∀ k < 3, (j2FiveRS 4)[k]! = unpack 315 9 (C4.S k) := fun k hk => binds4.2.2.2.2.1 k
    (by omega)
  have hq : ∀ k < 3, eqA 315 (unpack 315 9 (C4.S k)) (unpack 315 9 (GR k)) = true :=
    fun k hk => eqA_of (gens4 k hk).1 (gens4 k hk).2.1 (gens4 k hk).2.2
  rw [caseChainOK3, hW, hc, Bool.true_and, hS 0 (by norm_num), hS 1 (by norm_num),
    hS 2 (by norm_num), hGR 0 (by norm_num), hGR 1 (by norm_num), hGR 2 (by norm_num),
    hq 0 (by norm_num), hq 1 (by norm_num), hq 2 (by norm_num)]
  rfl

theorem cent4 : centOKP 5 315 (j2FiveRS 4) ((j2FiveRBase 4).map Fin.val).toArray (j2FiveX 4)
    (j2FiveRRels 4) (j2FiveCG 4) j2FiveKeyPts (j2FiveCCert 4) 50 = true := by
  have hbase := binds4.2.2.2.2.2
  have hbr : ∀ k < rcnt (C4.LR 0), br4 k = true := by
    rw [Nat.eq_of_beq_eq_true rc4]
    exact forall_of_chunks 63 5 _ fun c hc => by
      interval_cases c
      · exact br4_0
      · exact br4_1
      · exact br4_2
      · exact br4_3
      · exact br4_4
  have hxs : ∀ e < (CFSG.RankThree.PartOne.powPA 5 315 (j2FiveX 4)).size,
      (CFSG.RankThree.PartOne.powPA 5 315 (j2FiveX 4))[e]! = unpack 315 9 (pw (LX 4) e) := by
    rw [hLX 4 (by norm_num)]
    exact powPA_get lx4
  have hlt : ∀ r ∈ j2FiveRRels 4, r.2.2 < (CFSG.RankThree.PartOne.powPA 5 315 (j2FiveX 4)).size :=
    fun r hr => by simpa [CFSG.RankThree.PartOne.powPA] using rel_lt_of rels4 r hr
  have htail := ptailK_sound binds4 perm4 C4.hl (hLX 4 (by norm_num)) lx4 hxs hlt
    (toList_of bC4.1 bC4.2.1) pC4 (by norm_num) hbr
  simp only [centOKP, Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨?_, enumC4⟩, bC4.1⟩, ?_⟩, ?_⟩, by rw [bsz4]; exact htail⟩
  · rw [hLX 4 (by norm_num)]
    exact relsOKP_of bsz4 hbase.2 bpt4 lx4 rels4
  · rw [allLt_iff]
    intro k hk
    rw [hCG4 k hk, hLX 4 (by norm_num)]
    rw [cgs4] at hk
    exact comm_of (comm4 k hk).1 lx4 (comm4 k hk).2
  · rw [allLt_iff]
    intro k hk
    rw [hCG4 k hk]
    rw [cgs4] at hk
    exact siftK_soundR binds4 perm4 C4.hl rfl (Nat.eq_of_beq_eq_true (sift4 k hk).1)
      (sift4 k hk).2.1 (sift4 k hk).2.2

end CertificateChecks.KernelMisc.J2F

end
