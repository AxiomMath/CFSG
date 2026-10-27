module

public import Certificates.Kernel.Misc.Perm.J5K3
public import Certificates.Kernel.Misc.Perm.J5H
import CFSG.Certificates.Kernel.Spor.SiftRSound

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.J2F

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Misc.ArrEnum CFSG.KC.Misc.ChainTail
open CFSG.RankThree.PartOne CFSG.RankThree.Native CFSG.Monster.B.Co2.Native
open CFSG.KC.Misc.Clos (forall_of_chunks)
open CFSG.Monster.B.Co2 (allLt_iff)

theorem binds3 : Binds 315 9 C3.S 7 4 C3.BP (j2FiveRS 3) ((j2FiveRBase 3).map Fin.val).toArray :=
  ⟨by norm_num, by norm_num, by norm_num, Nat.eq_of_beq_eq_true rsz3,
    fun j hj => arrBind_sound (rbind3 j hj), bsz3, bget3⟩

theorem chain3 : caseChainOK3 315 (j2FiveRS 3) ((j2FiveRBase 3).map Fin.val).toArray (j2FiveRW 3)
    j2FiveGensR[0]! j2FiveGensR[1]! j2FiveGensR[2]! = true := by
  have hc := rawChainK_sound (chunks := 1) binds3 C3.head C3.hl (by norm_num) C3.hs
  have hW : j2FiveRW 3 = CFSG.Sporadic.Schreier.Co3.Native.wordsArr 3 7 j2FiveRW3 := by
    have hs : (j2FiveRS 3).size = 7 := Nat.eq_of_beq_eq_true rsz3
    rw [j2FiveRW, hs]
    rfl
  have hS : ∀ k < 3, (j2FiveRS 3)[k]! = unpack 315 9 (C3.S k) := fun k hk => binds3.2.2.2.2.1 k
    (by omega)
  have hq : ∀ k < 3, eqA 315 (unpack 315 9 (C3.S k)) (unpack 315 9 (GR k)) = true :=
    fun k hk => eqA_of (gens3 k hk).1 (gens3 k hk).2.1 (gens3 k hk).2.2
  rw [caseChainOK3, hW, hc, Bool.true_and, hS 0 (by norm_num), hS 1 (by norm_num),
    hS 2 (by norm_num), hGR 0 (by norm_num), hGR 1 (by norm_num), hGR 2 (by norm_num),
    hq 0 (by norm_num), hq 1 (by norm_num), hq 2 (by norm_num)]
  rfl

theorem cent3 : centOKP 5 315 (j2FiveRS 3) ((j2FiveRBase 3).map Fin.val).toArray (j2FiveX 3)
    (j2FiveRRels 3) (j2FiveCG 3) j2FiveKeyPts (j2FiveCCert 3) 300 = true := by
  have hbase := binds3.2.2.2.2.2
  have hbr : ∀ k < rcnt (C3.LR 0), br3 k = true := by
    rw [Nat.eq_of_beq_eq_true rc3]
    exact forall_of_chunks 63 5 _ fun c hc => by
      interval_cases c
      · exact br3_0
      · exact br3_1
      · exact br3_2
      · exact br3_3
      · exact br3_4
  have hxs : ∀ e < (CFSG.RankThree.PartOne.powPA 5 315 (j2FiveX 3)).size,
      (CFSG.RankThree.PartOne.powPA 5 315 (j2FiveX 3))[e]! = unpack 315 9 (pw (LX 3) e) := by
    rw [hLX 3 (by norm_num)]
    exact powPA_get lx3
  have hlt : ∀ r ∈ j2FiveRRels 3, r.2.2 < (CFSG.RankThree.PartOne.powPA 5 315 (j2FiveX 3)).size :=
    fun r hr => by simpa [CFSG.RankThree.PartOne.powPA] using rel_lt_of rels3 r hr
  have htail := ptailK_sound binds3 perm3 C3.hl (hLX 3 (by norm_num)) lx3 hxs hlt
    (toList_of bC3.1 bC3.2.1) pC3 (by norm_num) hbr
  simp only [centOKP, Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨?_, enumC3⟩, bC3.1⟩, ?_⟩, ?_⟩, by rw [bsz3]; exact htail⟩
  · rw [hLX 3 (by norm_num)]
    exact relsOKP_of bsz3 hbase.2 bpt3 lx3 rels3
  · rw [allLt_iff]
    intro k hk
    rw [hCG3 k hk, hLX 3 (by norm_num)]
    rw [cgs3] at hk
    exact comm_of (comm3 k hk).1 lx3 (comm3 k hk).2
  · rw [allLt_iff]
    intro k hk
    rw [hCG3 k hk]
    rw [cgs3] at hk
    exact siftK_soundR binds3 perm3 C3.hl rfl (Nat.eq_of_beq_eq_true (sift3 k hk).1)
      (sift3 k hk).2.1 (sift3 k hk).2.2

end CertificateChecks.KernelMisc.J2F

end
