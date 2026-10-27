module

public import Certificates.Kernel.Misc.Perm.J5K0
public import Certificates.Kernel.Misc.Perm.J5H
import CFSG.Certificates.Kernel.Spor.SiftRSound

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.J2F

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Misc.ArrEnum CFSG.KC.Misc.ChainTail
open CFSG.RankThree.PartOne CFSG.RankThree.Native CFSG.Monster.B.Co2.Native
open CFSG.KC.Misc.Clos (forall_of_chunks)
open CFSG.Monster.B.Co2 (allLt_iff)

theorem binds0 : Binds 315 9 C0.S 6 4 C0.BP (j2FiveRS 0) ((j2FiveRBase 0).map Fin.val).toArray :=
  ⟨by norm_num, by norm_num, by norm_num, Nat.eq_of_beq_eq_true rsz0,
    fun j hj => arrBind_sound (rbind0 j hj), bsz0, bget0⟩

theorem chain0 : caseChainOK3 315 (j2FiveRS 0) ((j2FiveRBase 0).map Fin.val).toArray (j2FiveRW 0)
    j2FiveGensR[0]! j2FiveGensR[1]! j2FiveGensR[2]! = true := by
  have hc := rawChainK_sound (chunks := 1) binds0 C0.head C0.hl (by norm_num) C0.hs
  have hW : j2FiveRW 0 = CFSG.Sporadic.Schreier.Co3.Native.wordsArr 3 6 j2FiveRW0 := by
    have hs : (j2FiveRS 0).size = 6 := Nat.eq_of_beq_eq_true rsz0
    rw [j2FiveRW, hs]
    rfl
  have hS : ∀ k < 3, (j2FiveRS 0)[k]! = unpack 315 9 (C0.S k) := fun k hk => binds0.2.2.2.2.1 k
    (by omega)
  have hq : ∀ k < 3, eqA 315 (unpack 315 9 (C0.S k)) (unpack 315 9 (GR k)) = true :=
    fun k hk => eqA_of (gens0 k hk).1 (gens0 k hk).2.1 (gens0 k hk).2.2
  rw [caseChainOK3, hW, hc, Bool.true_and, hS 0 (by norm_num), hS 1 (by norm_num),
    hS 2 (by norm_num), hGR 0 (by norm_num), hGR 1 (by norm_num), hGR 2 (by norm_num),
    hq 0 (by norm_num), hq 1 (by norm_num), hq 2 (by norm_num)]
  rfl

theorem cent0 : centOKP 5 315 (j2FiveRS 0) ((j2FiveRBase 0).map Fin.val).toArray (j2FiveX 0)
    (j2FiveRRels 0) (j2FiveCG 0) j2FiveKeyPts (j2FiveCCert 0) 50 = true := by
  have hbase := binds0.2.2.2.2.2
  have hbr : ∀ k < rcnt (C0.LR 0), br0 k = true := by
    rw [Nat.eq_of_beq_eq_true rc0]
    exact forall_of_chunks 63 5 _ fun c hc => by
      interval_cases c
      · exact br0_0
      · exact br0_1
      · exact br0_2
      · exact br0_3
      · exact br0_4
  have hxs : ∀ e < (CFSG.RankThree.PartOne.powPA 5 315 (j2FiveX 0)).size,
      (CFSG.RankThree.PartOne.powPA 5 315 (j2FiveX 0))[e]! = unpack 315 9 (pw (LX 0) e) := by
    rw [hLX 0 (by norm_num)]
    exact powPA_get lx0
  have hlt : ∀ r ∈ j2FiveRRels 0, r.2.2 < (CFSG.RankThree.PartOne.powPA 5 315 (j2FiveX 0)).size :=
    fun r hr => by simpa [CFSG.RankThree.PartOne.powPA] using rel_lt_of rels0 r hr
  have htail := ptailK_sound binds0 perm0 C0.hl (hLX 0 (by norm_num)) lx0 hxs hlt
    (toList_of bC0.1 bC0.2.1) pC0 (by norm_num) hbr
  simp only [centOKP, Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨?_, enumC0⟩, bC0.1⟩, ?_⟩, ?_⟩, by rw [bsz0]; exact htail⟩
  · rw [hLX 0 (by norm_num)]
    exact relsOKP_of bsz0 hbase.2 bpt0 lx0 rels0
  · rw [allLt_iff]
    intro k hk
    rw [hCG0 k hk, hLX 0 (by norm_num)]
    rw [cgs0] at hk
    exact comm_of (comm0 k hk).1 lx0 (comm0 k hk).2
  · rw [allLt_iff]
    intro k hk
    rw [hCG0 k hk]
    rw [cgs0] at hk
    exact siftK_soundR binds0 perm0 C0.hl rfl (Nat.eq_of_beq_eq_true (sift0 k hk).1)
      (sift0 k hk).2.1 (sift0 k hk).2.2

end CertificateChecks.KernelMisc.J2F

end
