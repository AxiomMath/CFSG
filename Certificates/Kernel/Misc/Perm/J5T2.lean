module

public import Certificates.Kernel.Misc.Perm.J5K2
public import Certificates.Kernel.Misc.Perm.J5H
import CFSG.Certificates.Kernel.Spor.SiftRSound

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.J2F

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Misc.ArrEnum CFSG.KC.Misc.ChainTail
open CFSG.RankThree.PartOne CFSG.RankThree.Native CFSG.Monster.B.Co2.Native
open CFSG.KC.Misc.Clos (forall_of_chunks)
open CFSG.Monster.B.Co2 (allLt_iff)

theorem binds2 : Binds 315 9 C2.S 8 4 C2.BP (j2FiveRS 2) ((j2FiveRBase 2).map Fin.val).toArray :=
  ⟨by norm_num, by norm_num, by norm_num, Nat.eq_of_beq_eq_true rsz2,
    fun j hj => arrBind_sound (rbind2 j hj), bsz2, bget2⟩

theorem chain2 : caseChainOK3 315 (j2FiveRS 2) ((j2FiveRBase 2).map Fin.val).toArray (j2FiveRW 2)
    j2FiveGensR[0]! j2FiveGensR[1]! j2FiveGensR[2]! = true := by
  have hc := rawChainK_sound (chunks := 1) binds2 C2.head C2.hl (by norm_num) C2.hs
  have hW : j2FiveRW 2 = CFSG.Sporadic.Schreier.Co3.Native.wordsArr 3 8 j2FiveRW2 := by
    have hs : (j2FiveRS 2).size = 8 := Nat.eq_of_beq_eq_true rsz2
    rw [j2FiveRW, hs]
    rfl
  have hS : ∀ k < 3, (j2FiveRS 2)[k]! = unpack 315 9 (C2.S k) := fun k hk => binds2.2.2.2.2.1 k
    (by omega)
  have hq : ∀ k < 3, eqA 315 (unpack 315 9 (C2.S k)) (unpack 315 9 (GR k)) = true :=
    fun k hk => eqA_of (gens2 k hk).1 (gens2 k hk).2.1 (gens2 k hk).2.2
  rw [caseChainOK3, hW, hc, Bool.true_and, hS 0 (by norm_num), hS 1 (by norm_num),
    hS 2 (by norm_num), hGR 0 (by norm_num), hGR 1 (by norm_num), hGR 2 (by norm_num),
    hq 0 (by norm_num), hq 1 (by norm_num), hq 2 (by norm_num)]
  rfl

theorem cent2 : centOKP 5 315 (j2FiveRS 2) ((j2FiveRBase 2).map Fin.val).toArray (j2FiveX 2)
    (j2FiveRRels 2) (j2FiveCG 2) j2FiveKeyPts (j2FiveCCert 2) 300 = true := by
  have hbase := binds2.2.2.2.2.2
  have hbr : ∀ k < rcnt (C2.LR 0), br2 k = true := by
    rw [Nat.eq_of_beq_eq_true rc2]
    exact forall_of_chunks 63 5 _ fun c hc => by
      interval_cases c
      · exact br2_0
      · exact br2_1
      · exact br2_2
      · exact br2_3
      · exact br2_4
  have hxs : ∀ e < (CFSG.RankThree.PartOne.powPA 5 315 (j2FiveX 2)).size,
      (CFSG.RankThree.PartOne.powPA 5 315 (j2FiveX 2))[e]! = unpack 315 9 (pw (LX 2) e) := by
    rw [hLX 2 (by norm_num)]
    exact powPA_get lx2
  have hlt : ∀ r ∈ j2FiveRRels 2, r.2.2 < (CFSG.RankThree.PartOne.powPA 5 315 (j2FiveX 2)).size :=
    fun r hr => by simpa [CFSG.RankThree.PartOne.powPA] using rel_lt_of rels2 r hr
  have htail := ptailK_sound binds2 perm2 C2.hl (hLX 2 (by norm_num)) lx2 hxs hlt
    (toList_of bC2.1 bC2.2.1) pC2 (by norm_num) hbr
  simp only [centOKP, Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨?_, enumC2⟩, bC2.1⟩, ?_⟩, ?_⟩, by rw [bsz2]; exact htail⟩
  · rw [hLX 2 (by norm_num)]
    exact relsOKP_of bsz2 hbase.2 bpt2 lx2 rels2
  · rw [allLt_iff]
    intro k hk
    rw [hCG2 k hk, hLX 2 (by norm_num)]
    rw [cgs2] at hk
    exact comm_of (comm2 k hk).1 lx2 (comm2 k hk).2
  · rw [allLt_iff]
    intro k hk
    rw [hCG2 k hk]
    rw [cgs2] at hk
    exact siftK_soundR binds2 perm2 C2.hl rfl (Nat.eq_of_beq_eq_true (sift2 k hk).1)
      (sift2 k hk).2.1 (sift2 k hk).2.2

end CertificateChecks.KernelMisc.J2F

end
