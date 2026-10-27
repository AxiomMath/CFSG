
module

public import Certificates.Kernel.SporSch.Co2M.FratC
public import Certificates.Kernel.SporSch.Co2M.FratSA
public import Certificates.Kernel.SporSch.Co2M.FratSB
public import Certificates.Kernel.SporSch.Co2M.FratSC
public import Certificates.Kernel.SporSch.Co2M.FratYB1
public import Certificates.Kernel.SporSch.Co2M.ChainS
public import CFSG.Certificates.Kernel.Spor.PackWord
public import CFSG.Certificates.Kernel.Spor.RawSiftKConv
public import CFSG.Certificates.Kernel.Spor.PrimSound
public import CFSG.Certificates.Kernel.SporSch.Co2ProfSound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Co2M

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Co2M CFSG.KS.MatRep CFSG.KS.Prim CFSG.KC.BfsPin
open CFSG.Sporadic.Co2Schreier CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

theorem zs_ok : allN 15 (fun j => Nat.beq (cmpP zP (sT.getD j (0, 0))).1
    (cmpP (sT.getD j (0, 0)) zP).1) = true := by
  quickRfl

noncomputable abbrev canon (p : ℕ) : Bool := canonK 2300 12 (mask 12) (2300 * 12) p

theorem pc_eq (p q : ℕ) : pc p q = pcomp 2300 12 (mask 12) p q := by
  unfold pc
  rw [CFSG.KS.Co2P.strictN_eq, CFSG.KS.Co2P.strictN_eq]

theorem canon_pc {p q : ℕ} (hp : canon p = true) (hq : canon q = true) : canon (pc p q) = true := by
  rw [pc_eq]
  exact canonK_pcomp hp hq

theorem unpack_pc {p q : ℕ} (hp : canon p = true) (hq : canon q = true) :
    compA 2300 (unpack 2300 12 p) (unpack 2300 12 q) = unpack 2300 12 (pc p q) := by
  rw [pc_eq]
  exact compA_unpack hp hq

theorem siftF_eq (G : ℕ) : siftF G =
    siftK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) Co2LF.LR Co2LF.TRI Co2LF.BP 2 0 G :=
  CFSG.KS.Co2P.strictB_eq _ _

theorem sift_yes {G : ℕ} (hc : canon G = true) (h : siftF G = true) :
    siftA 2300 fratLevels fratBase 0 (unpack 2300 12 G) = true :=
  siftK_sound Co2LF.binds Co2LF.perm Co2LF.hl rfl (range_of_canonK hc) (by rwa [siftF_eq] at h)

theorem sift_no {G : ℕ} (hc : canon G = true) (h : siftF G = false) :
    siftA 2300 fratLevels fratBase 0 (unpack 2300 12 G) = false :=
  Orb.siftA_false_of_K Co2LF.binds Co2LF.perm Co2LF.hl (by decide +kernel)
    (CFSG.KS.PF.canon_facts hc).2.2.1 (range_of_canonK hc) (by rwa [siftF_eq] at h)

theorem canons : (∀ j < 15, canon (Co2LS.S j) = true ∧ canon (Co2LS.SI j) = true) ∧
    (∀ k < 12, canon (Co2LF.S k) = true) ∧ ∀ k < 64, canon (FY k) = true := by
  have h := canon_ok
  simp only [Bool.and_eq_true] at h
  exact ⟨fun j hj => (bAnd_iff _ _).1 (allN_spec h.1.1 j hj), allN_spec h.1.2,
    allN_spec h.2⟩

theorem s_eq {j : ℕ} (hj : j < 15) : sArrs[j]! = unpack 2300 12 (Co2LS.S j) :=
  (unpack_eq (repT_get sRep (by rw [sT_len]; exact hj)) (allN_spec orig_s j hj)).symm

theorem si_eq {j : ℕ} (hj : j < 15) : invCand 2300 sArrs[j]! = unpack 2300 12 (Co2LS.SI j) := by
  rw [s_eq hj]
  exact (invEqK_sound (allN_spec Co2LS.perm j (by omega))).1

theorem f_eq {k : ℕ} (hk : k < 12) : fratOrig[k]! = unpack 2300 12 (Co2LF.S k) := by
  have hs : k < fratOrig.size := by rw [fratOrigRep.1, fratT0_len]; exact hk
  rw [← extendArrs_get_lt fratOrig fratDerivs hs]
  exact Co2LF.S_eq (by omega)

theorem y_eq (w : ℕ) (hw : w < 32) : yArr w = unpack 2300 12 (FY w) := by
  have h := yb
  simp only [Bool.and_eq_true] at h
  have h2 := allN_spec h.1 w hw
  rw [Bool.and_eq_true] at h2
  exact (unpack_eq (yRep w) h2.1).symm

theorem yi_eq (w : ℕ) (hw : w < 32) : invCand 2300 (yArr w) = unpack 2300 12 (FY (32 + w)) :=
  (unpack_eq (rep_inv (yRep w)) (allN_spec yib w hw)).symm

theorem frat_check : fratCheck fratLevels = true := by
  obtain ⟨cS, cF, cY⟩ := canons
  unfold fratCheck
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨Co2LF.chain_ok, ?_⟩, allInv_of_repT fratOrigRep⟩,
    allInv_of_repT fratRep⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [Co2LF.orbits_ok]
    rfl
  · rw [fratOrigRep.1, fratT0_len]
    rfl
  · rw [yBRep.1, yBT_len]
    rfl
  · rw [CFSG.Monster.B.Co2.allLt_iff]
    intro j hj
    rw [CFSG.Monster.B.Co2.allLt_iff]
    intro k hk
    have e : compA 2300 (compA 2300 sArrs[j]! fratOrig[k]!) (invCand 2300 sArrs[j]!) =
        unpack 2300 12 (pc (pc (Co2LS.S j) (Co2LF.S k)) (Co2LS.SI j)) := by
      rw [si_eq hj, s_eq hj, f_eq hk, unpack_pc (cS j hj).1 (cF k hk),
        unpack_pc (canon_pc (cS j hj).1 (cF k hk)) (cS j hj).2]
    rw [e]
    exact sift_yes (canon_pc (canon_pc (cS j hj).1 (cF k hk)) (cS j hj).2)
      (allN_spec (allN_spec conj_ok j hj) k hk)
  · rw [CFSG.Monster.B.Co2.allLt_iff]
    intro i hi
    rw [CFSG.Monster.B.Co2.allLt_iff]
    intro j hj
    have c1 := canon_pc (cS i hi).1 (cS j hj).1
    have c2 := canon_pc c1 (cS i hi).2
    have e : compA 2300 (compA 2300 (compA 2300 sArrs[i]! sArrs[j]!) (invCand 2300 sArrs[i]!))
        (invCand 2300 sArrs[j]!) =
        unpack 2300 12 (pc (pc (pc (Co2LS.S i) (Co2LS.S j)) (Co2LS.SI i)) (Co2LS.SI j)) := by
      rw [si_eq hi, si_eq hj, s_eq hi, s_eq hj, unpack_pc (cS i hi).1 (cS j hj).1,
        unpack_pc c1 (cS i hi).2, unpack_pc c2 (cS j hj).2]
    rw [e]
    exact sift_yes (canon_pc c2 (cS j hj).2) (allN_spec (allN_spec comm_ok i hi) j hj)
  · rw [CFSG.Monster.B.Co2.allLt_iff]
    intro j hj
    have e : sqArr sArrs[j]! = unpack 2300 12 (pc (Co2LS.S j) (Co2LS.S j)) := by
      rw [sqArr, s_eq hj, unpack_pc (cS j hj).1 (cS j hj).1]
    rw [e]
    exact sift_yes (canon_pc (cS j hj).1 (cS j hj).1) (allN_spec sq_ok j hj)
  · rw [CFSG.Monster.B.Co2.allLt_iff]
    exact fun u _ => isInvA_rep (yRep u)
  · rw [CFSG.Monster.B.Co2.allLt_iff]
    intro u hu
    rw [CFSG.Monster.B.Co2.allLt_iff]
    intro v hv
    by_cases huv : u < v
    · have e : compA 2300 (invCand 2300 (yArr u)) (yArr v) =
          unpack 2300 12 (pc (FY (32 + u)) (FY v)) := by
        rw [yi_eq u hu, y_eq v hv, unpack_pc (cY _ (by omega)) (cY v (by omega))]
      have hn : siftA 2300 fratLevels fratBase 0 (compA 2300 (invCand 2300 (yArr u)) (yArr v)) =
          false := by
        rw [e]
        refine sift_no (canon_pc (cY _ (by omega)) (cY v (by omega))) ?_
        have h : Bool.rec (motive := fun _ => Bool) true
            (Bool.rec (motive := fun _ => Bool) true false (siftF (pc (FY (Nat.add 32 u)) (FY v))))
            (Nat.blt u v) = true := allN_spec (allN_spec pair_ok u hu) v hv
        have hb : Nat.blt u v = true := Nat.blt_eq.mpr huv
        rw [hb] at h
        change Bool.rec (motive := fun _ => Bool) true false
          (siftF (pc (FY (Nat.add 32 u)) (FY v))) = true at h
        cases hs : siftF (pc (FY (Nat.add 32 u)) (FY v))
        · rfl
        · rw [hs] at h
          exact absurd h (by decide)
      rw [hn]
      simp
    · simp [huv]
  · rw [CFSG.Monster.B.Co2.allLt_iff]
    intro j hj
    unfold commA
    have hj' : j < sT.length := by rw [sT_len]; exact hj
    exact eqA_of_mat (rep_cmp zRep (repT_get sRep hj')) (rep_cmp (repT_get sRep hj') zRep)
      (Nat.eq_of_beq_eq_true (allN_spec zs_ok j hj))

end CertificateChecks.KernelSporSch.Co2M

end
