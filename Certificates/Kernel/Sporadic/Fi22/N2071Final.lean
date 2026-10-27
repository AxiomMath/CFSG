module

public import Certificates.Kernel.Sporadic.Fi22.N2071Chk
public import Certificates.Kernel.Sporadic.Fi22.N2071Sift
public import Certificates.Kernel.Sporadic.Fi22.N2070Final
public import Certificates.Kernel.Sporadic.Fi22.C2079B
public import CFSG.Certificates.Kernel.Fi22Search2071Sound
public import CFSG.Sporadic.FischerOddCore.Fi22SearchCheckInputs
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.N2071

open CFSG.KC.Enum CFSG.KC.N3153 CFSG.KC.S2071 CFSG.KD.N3153 CFSG.KS CFSG.KS.Text CFSG.KS.Raw
open CFSG.KS.Prim CFSG.KC.BfsPin CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2
open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
open CFSG.Sporadic.FischerOddCore CFSG.Sporadic.FischerOddCore.Native
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Fi22X

theorem pp_all : allN 66 (fun j => Nat.beq (PP j) (Fi22CentT.L (Nat.add 240 j))) = true := by
  quickRfl

theorem pp_eq {j : Nat} (hj : j < 66) : PP j = Fi22CentT.L (240 + j) :=
  Nat.eq_of_beq_eq_true (CFSG.KC.Pack.allN_spec pp_all j hj)

theorem pp66 : PP 66 = Fi22ExtT.L 21 := Nat.eq_of_beq_eq_true (by quickRfl)

theorem t_eq : fi22ExtArr 21 = unpack 3510 12 (PP 66) := by
  rw [pp66]
  exact Fi22E2067.ext_eq (L := 21) (by norm_num)

theorem pool_eq {j : Nat} (hj : j < 64) : fi22SearchPoolArr[j]! = unpack 3510 12 (PP j) := by
  rw [fi22SearchPoolArr, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
  change fi22CentArr (240 + j) = _
  rw [N2070.cent_eq (by omega), pp_eq (by omega)]

theorem acc_eq {i : Nat} (hi : i < 2) : fi22CentArr (304 + i) = unpack 3510 12 (PP (64 + i)) := by
  rw [N2070.cent_eq (by omega), pp_eq (by omega), show 240 + (64 + i) = 304 + i by omega]

theorem accArr_eq {i : Nat} (hi : i < 2) : fi22SearchAccArr[i]! = unpack 3510 12 (PP (64 + i)) := by
  rw [fi22SearchAccArr, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
  exact acc_eq hi

theorem nodes_size : fi22SearchNodes.size = 138 := rfl

theorem search :
    searchOK 3510 fi22Nbr (fi22ExtArr 21) fi22SearchBase fi22SearchPoolArr fi22SearchNodes
      fi22SearchAccArr 4 4 = true := by
  refine search_sound (d := 693) (np := 64) (na := 2) (T := PP 66) (P := CFSG.KD.S2071.O 0)
    (SC := srcCols) (R := R) (M := M) (S := S) (PL := fun j => PP j) (AC := fun i => PP (64 + i))
    (DT := CFSG.KD.S2071.D) (by norm_num) (by norm_num) (by norm_num) (by norm_num) N3153.nbr_eq
    N3153.rows N3153.symm t_eq (by decide) (by decide +kernel) (by decide +kernel) (by norm_num)
    (by simp [fi22SearchPoolArr]) (fun j hj => pool_eq hj) (by simp [fi22SearchAccArr])
    (fun i hi => accArr_eq hi) ?_ ?_ (by rw [nodes_size]; norm_num) (by decide +kernel) ?_
  · have h := inj
    rw [N3153.strictB_eq] at h
    exact h
  · intro e he
    have h := Src.all e (by simpa [fi22SearchBase] using he)
    rw [srcB, N3153.strictB_eq] at h
    exact h
  · intro i hi
    have h := Node.all i (by rwa [nodes_size] at hi)
    rw [nodeB, N3153.strictB_eq] at h
    exact h

theorem pool_sift :
    ∀ j < 64, siftA 3510 (rawLevels 3510 (fi22CentStrong 0) #[0, 1, 2, 3, 6, 4]) #[0, 1, 2, 3, 6, 4]
      0 (fi22CentArr (240 + j)) = true := by
  intro j hj
  have h := CFSG.KC.Pack.allN_spec N2071.pool j hj
  simp only [bAnd_iff] at h
  obtain ⟨hc, hperm, hsp, hbk⟩ : cn (Fi22CentT.L (240 + j)) = true ∧
      permOK 3510 12 (mask 12) (3510 * 12) (Fi22CentT.L (240 + j)) (inv (Fi22CentT.L (240 + j))) =
        true ∧ siftP (Fi22CentT.L (240 + j)) = true ∧
      siftBK 3510 12 (mask 12) (3510 * 12) 6 Fi22H0.S Fi22H0.SI Fi22H0.LR Fi22H0.ST 19 6 0
        (baseImK 12 (mask 12) 6 (Fi22CentT.L (240 + j)) Fi22H0.BP) = true := h
  have hrep := (Fo22C.rep_of_perm hperm).1
  have hb : Binds 3510 12 Fi22H0.S 19 6 Fi22H0.BP (fi22CentStrong 0) #[0, 1, 2, 3, 6, 4] :=
    Fo22C.bindsH Fi22CentB.text_eq (st := 0) (by norm_num) rfl rfl (by norm_num) Fi22C2066.b0
      Fi22C2066.p0
  rw [N2070.cent_eq (by omega)]
  exact (siftA_iff_mem_fi22H (c := 0) (by norm_num) hrep).2
    (Fo22C.mem_H (c := 0) (by norm_num) hb Fi22H0.head Fi22H0.tl Fi22H0.hst hrep
      (Fo22C.mem_P hc hsp hperm) hbk)

theorem acc_facts :
    (∀ i < 2, (allLt 3510 fun x =>
        fi22Nbr[(fi22CentArr (304 + i))[x]!]! == imgSorted (fi22CentArr (304 + i)) fi22Nbr[x]!) =
          true ∧
        eqA 3510 (compA 3510 (fi22CentArr (304 + i)) (fi22ExtArr 21))
          (compA 3510 (fi22ExtArr 21) (fi22CentArr (304 + i))) = true) ∧
      fi22InP (fi22CentArr 304) = true ∧ fi22InP (fi22CentArr 305) = false ∧
      fi22InP (compA 3510 fi22GraphOuterArr (fi22CentArr 305)) = true := by
  have hcA : ∀ i < 2, cn (Fi22CentT.L (304 + i)) = true := fun i hi =>
    CFSG.KC.Pack.allN_spec cnA i hi
  have eT := Fi22E2067.ext_eq (L := 21) (by norm_num)
  have e4 := N2070.cent_eq (L := 304) (by norm_num)
  have e5 := N2070.cent_eq (L := 305) (by norm_num)
  have c5 := hcA 1 (by norm_num)
  refine ⟨fun i hi => ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [N3153.nbr_eq]
    have himg : ∀ x < 3510, imgOK 3510 693 (PP (64 + i)) R M x = true := by
      interval_cases i
      · exact N3153.of_blocks ImgA0.all
      · exact N3153.of_blocks ImgA1.all
    exact img_sound (P := PP (64 + i)) (by norm_num) N3153.rows (acc_eq hi) himg
  · rw [N2070.cent_eq (by omega), eT, comp_eq (hcA i hi) cnT0, comp_eq cnT0 (hcA i hi)]
    exact eqA_of (cn_c (hcA i hi) cnT0) (cn_c cnT0 (hcA i hi)) (CFSG.KC.Pack.allN_spec comm i hi)
  · rw [fi22InP, e4, siftK_eq bindsP permP Fi22PC.hl rfl (hi_of (hcA 0 (by norm_num)))
      (range_of_canonK (hcA 0 (by norm_num)))]
    exact s0
  · rw [fi22InP, e5, siftK_eq bindsP permP Fi22PC.hl rfl (hi_of c5) (range_of_canonK c5)]
    exact N2070.not_true s1
  · rw [fi22InP, go_eq, e5, comp_eq cnG c5, siftK_eq bindsP permP Fi22PC.hl rfl
      (hi_of (cn_c cnG c5)) (range_of_canonK (cn_c cnG c5))]
    exact s2

theorem facts2071 :
    searchOK 3510 fi22Nbr (fi22ExtArr 21) fi22SearchBase fi22SearchPoolArr fi22SearchNodes
      fi22SearchAccArr 4 4 = true ∧
    (∀ j < 64, siftA 3510 (rawLevels 3510 (fi22CentStrong 0) #[0, 1, 2, 3, 6, 4])
      #[0, 1, 2, 3, 6, 4] 0 (fi22CentArr (240 + j)) = true) ∧
    ((∀ i < 2, (allLt 3510 fun x =>
        fi22Nbr[(fi22CentArr (304 + i))[x]!]! == imgSorted (fi22CentArr (304 + i)) fi22Nbr[x]!) =
          true ∧
        eqA 3510 (compA 3510 (fi22CentArr (304 + i)) (fi22ExtArr 21))
          (compA 3510 (fi22ExtArr 21) (fi22CentArr (304 + i))) = true) ∧
      fi22InP (fi22CentArr 304) = true ∧ fi22InP (fi22CentArr 305) = false ∧
      fi22InP (compA 3510 fi22GraphOuterArr (fi22CentArr 305)) = true) :=
  ⟨search, pool_sift, acc_facts⟩

end CertificateChecks.KernelSpor.N2071

end
