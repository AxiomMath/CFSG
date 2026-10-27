module

public import Certificates.Kernel.Sporadic.Fi22.P2066
public import CFSG.Certificates.Kernel.Spor.BaseSep
public import CFSG.Sporadic.FischerOddCore.Fi22Cent
public import CFSG.Sporadic.FischerOddCore.Fi22CentOrderCheckInputs
public import CFSG.Monster.B.Fischer.Fi22Order
public import CFSG.Sporadic.FischerOddCore.Fi22CentOrderCheckInputs
public meta import CFSG.Sporadic.FischerOddCore.Fi22Cent
public meta import CFSG.Sporadic.FischerOddCore.Fi22ExtSylowCheck
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fi22C2066

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Fischer CFSG.Sporadic.FischerOddCore
open CertificateChecks.KernelSpor

theorem fi22P_sep
    {G : Equiv.Perm (Fin 3510)} (hG : G ∈ fi22P)
    (hfix : ∀ t < B.size, ∀ h : B[t]! < 3510, G ⟨B[t]!, h⟩ = ⟨B[t]!, h⟩) : G = 1 := by
  refine fi22Chain.eq_one_of_fixes_base fi22Chain_valid.1 hG fun i => ?_
  have hv : ((fi22Chain.base.get i : Fin 3510) : ℕ) = B[(i : ℕ)]! :=
    fi22ChainArrays.base_val i
  have hi : (i : ℕ) < B.size := i.2
  have e : fi22Chain.base.get i = ⟨B[(i : ℕ)]!, hv ▸ (fi22Chain.base.get i).2⟩ := Fin.ext hv
  rw [e]
  exact hfix i hi _

theorem fi22InP_of {PS : Nat → Nat} {j : Nat} {g : Array Nat} (hg : g = unpack 3510 12 (PS j))
    (hc : Fi22X.cn (PS j) = true) (hs : Fi22X.siftP (PS j) = true) : fi22InP g = true := by
  rw [fi22InP, siftK_eq Fi22X.bindsP Fi22X.permP Fi22PC.hl hg (Fi22X.hi_of hc)
    (range_of_canonK hc)]
  exact hs

theorem order_ok
    (htext : fi22Cent3510Text = Fi22E2065.textP) {c st kS kO cs BP : Nat}
    {PS PSI LR ST : Nat → Nat} (hc : c < 5) (hst : fi22CentStrongStart.getD c 0 = st)
    (hcnt : fi22CentStrongCount.getD c 0 = kS) (hk : fi22CentGenCount.getD c 0 = kO)
    (hcs : fi22CentCase c = cs) (hkk : kO ≤ kS) (hline : st + kS ≤ 306) (hcs6 : cs < 6)
    (hbind : allN kS (fun j => Nat.beq (PS j) (Fi22CentT.L (Nat.add st j))) = true)
    (hbase : allN 6 (fun t => Nat.beq B[t]! (pg 12 (mask 12) BP t)) = true)
    (hhead : headK 3510 12 (mask 12) (3510 * 12) (pidn 3510 12) PS PSI kS kO
      (fi22CentDerivations.getD c []) 6 BP = true)
    (htl : TreeOK 3510 12 PS PSI LR kS 6 BP) (hstp : StepsOK 3510 12 PS ST kS 6 BP)
    (hs : SchBOK 3510 12 6 PS PSI LR ST kS BP)
    (hcn : allN kS (fun j => Fi22X.cn (PS j)) = true)
    (hsift : allN kS (fun j => Fi22X.siftP (PS j)) = true)
    (hct : Fi22X.cn (Fi22ExtT.L (Nat.add 21 cs)) = true)
    (hcomm : allN kO (fun j => Nat.beq (Fi22X.c (PS j) (Fi22ExtT.L (Nat.add 21 cs)))
      (Fi22X.c (Fi22ExtT.L (Nat.add 21 cs)) (PS j))) = true)
    (hord : ((List.range 6).map fun i => rcnt (LR i)).prod = fi22CentOrders.getD c 0) :
    fi22CentOrderOK c = true := by
  have hsize : (fi22CentStrong c).size = kS := by
    rw [fi22CentStrong, Array.size_ofFn, hcnt]
  have hS : ∀ j < kS, (fi22CentStrong c)[j]! = unpack 3510 12 (PS j) := by
    intro j hj
    rw [fi22CentStrong_get hc (by rw [hcnt]; exact hj), fi22CentArr, fi22CentBytes, htext, hst,
      Fi22E2065.cent_eq (by omega), Nat.eq_of_beq_eq_true (allN_spec hbind j hj)]
    rfl
  have hb : Binds 3510 12 PS kS 6 BP (fi22CentStrong c) B :=
    ⟨by norm_num, by norm_num, by norm_num, hsize, hS, rfl,
      fun t ht => Nat.eq_of_beq_eq_true (allN_spec hbase t ht)⟩
  have hInP : ∀ j < kS, fi22InP (fi22CentStrong c)[j]! = true := fun j hj =>
    fi22InP_of (hS j hj) (allN_spec hcn j hj) (allN_spec hsift j hj)
  have hmem : ∀ j < kS, permOfArr 3510 (fi22CentStrong c)[j]! ∈ fi22P := by
    intro j hj
    have hinv : isInvA 3510 (fi22CentStrong c)[j]! (invCand 3510 (fi22CentStrong c)[j]!) = true := by
      refine Fi22E2067.isInv_of (P := Fi22CentT.L (st + j)) ?_ (Fi22E2065.perm (by omega))
      rw [hS j hj, Nat.eq_of_beq_eq_true (allN_spec hbind j hj)]
      rfl
    have hrep := (rep_permOfArr hinv).1
    exact (siftA_iff_mem_originalSubgroup fi22ChainArrays (by norm_num) fi22Order_check.1 hrep).1
      (hInP j hj)
  have hsep : Sep 3510 (fi22CentStrong c) B := by
    intro G hG hfix
    refine fi22P_sep ((Subgroup.closure_le _).2 ?_ hG) hfix
    rintro _ ⟨j, hj, rfl⟩
    exact hmem j (hsize ▸ hj)
  have hK : fi22CentK c = kO := by
    rw [fi22CentK, hsize, hk]
    omega
  have hW : fi22CentWords c =
      CFSG.Sporadic.Schreier.Co3.Native.wordsArr kO kS (fi22CentDerivations.getD c []) := by
    rw [fi22CentWords, hk, hcnt]
    rfl
  have h1 : rawChainOK 3510 ((fi22CentStrong c).extract 0 (fi22CentK c)) (fi22CentStrong c) B
      (fi22CentWords c) 4 = true := by
    rw [hK, hW]
    exact rawChainTK_sound hb hhead htl hstp hsep hs (by norm_num)
  have h2 : (rawOrbitSizes 3510 (fi22CentStrong c) B).prod = fi22CentOrders.getD c 0 := by
    rw [rawOrbitSizesTK_sound hb hhead htl, hord]
  have ht : fi22ExtArr (21 + fi22CentCase c) = unpack 3510 12 (Fi22ExtT.L (Nat.add 21 cs)) := by
    rw [hcs]
    exact Fi22E2067.ext_eq (by omega)
  have h3 : ∀ j < fi22CentGenCount.getD c 0, fi22InP (fi22CentStrong c)[j]! = true ∧
      eqA 3510 (compA 3510 (fi22CentStrong c)[j]! (fi22ExtArr (21 + fi22CentCase c)))
        (compA 3510 (fi22ExtArr (21 + fi22CentCase c)) (fi22CentStrong c)[j]!) = true := by
    intro j hj
    rw [hk] at hj
    have hj' : j < kS := by omega
    have cj := allN_spec hcn j hj'
    refine ⟨hInP j hj', ?_⟩
    rw [hS j hj', ht, Fi22X.comp_eq cj hct, Fi22X.comp_eq hct cj]
    exact Fi22X.eqA_of (Fi22X.cn_c cj hct) (Fi22X.cn_c hct cj) (allN_spec hcomm j hj)
  unfold fi22CentOrderOK
  simp only [Bool.and_eq_true, beq_iff_eq]
  exact ⟨⟨h1, h2⟩, allLt_iff.2 fun j hj => by simpa using h3 j hj⟩

theorem order_ok'
    (htext : fi22Cent3510Text = Fi22E2065.textP) {c st kS kO cs BP : Nat}
    {PS PSI LR ST : Nat → Nat} (hc : c < 5) (hst : fi22CentStrongStart.getD c 0 = st)
    (hcnt : fi22CentStrongCount.getD c 0 = kS) (hk : fi22CentGenCount.getD c 0 = kO)
    (hcs : fi22CentCase c = cs) (hkk : kO ≤ kS) (hline : st + kS ≤ 306) (hcs6 : cs < 6)
    (hbind : bindK PS kS st = true) (hbase : baseK BP = true)
    (hhead : headK 3510 12 (mask 12) (3510 * 12) (pidn 3510 12) PS PSI kS kO
      (fi22CentDerivations.getD c []) 6 BP = true)
    (htl : TreeOK 3510 12 PS PSI LR kS 6 BP) (hstp : StepsOK 3510 12 PS ST kS 6 BP)
    (hs : SchBOK 3510 12 6 PS PSI LR ST kS BP) (hp : inPK PS kS = true)
    (hm : commK PS kO cs = true)
    (hord : ((List.range 6).map fun i => rcnt (LR i)).prod = fi22CentOrders.getD c 0) :
    fi22CentOrderOK c = true := by
  obtain ⟨hcn, hsift⟩ := (bAnd_iff _ _).1 hp
  obtain ⟨hct, hcomm⟩ := (bAnd_iff _ _).1 hm
  exact order_ok htext hc hst hcnt hk hcs hkk hline hcs6 hbind hbase hhead htl hstp hs hcn hsift
    hct hcomm hord

theorem facts2066
    (htext : fi22Cent3510Text = Fi22E2065.textP) :
    fi22CentOrderOK 0 = true ∧ fi22CentOrderOK 1 = true ∧ fi22CentOrderOK 2 = true ∧
      fi22CentOrderOK 3 = true ∧ fi22CentOrderOK 4 = true :=
  ⟨order_ok' htext (st := 0) (kS := 19) (kO := 12) (cs := 0) (by norm_num) rfl rfl rfl rfl
      (by norm_num) (by norm_num) (by norm_num) b0 p0 Fi22H0.head Fi22H0.tl Fi22H0.hst Fi22H0.hs
      s0 m0 o0,
    order_ok' htext (st := 19) (kS := 16) (kO := 9) (cs := 1) (by norm_num) rfl rfl rfl rfl
      (by norm_num) (by norm_num) (by norm_num) b1 p1 Fi22H1.head Fi22H1.tl Fi22H1.hst Fi22H1.hs
      s1 m1 o1,
    order_ok' htext (st := 35) (kS := 9) (kO := 3) (cs := 3) (by norm_num) rfl rfl rfl rfl
      (by norm_num) (by norm_num) (by norm_num) b2 p2 Fi22H2.head Fi22H2.tl Fi22H2.hst Fi22H2.hs
      s2 m2 o2,
    order_ok' htext (st := 44) (kS := 19) (kO := 9) (cs := 4) (by norm_num) rfl rfl rfl rfl
      (by norm_num) (by norm_num) (by norm_num) b3 p3 Fi22H3.head Fi22H3.tl Fi22H3.hst Fi22H3.hs
      s3 m3 o3,
    order_ok' htext (st := 63) (kS := 16) (kO := 9) (cs := 5) (by norm_num) rfl rfl rfl rfl
      (by norm_num) (by norm_num) (by norm_num) b4 p4 Fi22H4.head Fi22H4.tl Fi22H4.hst Fi22H4.hs
      s4 m4 o4⟩

open CFSG CFSG.Sporadic CFSG.Sporadic.FischerOddCore CFSG.Monster.B.Co2.Native in
open CFSG.Certificates.Native CFSG.Monster.B.Fischer in
theorem certificate2066_of
    (htext : fi22Cent3510Text = Fi22E2065.textP) : (fi22CentOrderOK 0 = true)
    ∧ (fi22CentOrderOK 1 = true)
    ∧ (fi22CentOrderOK 2 = true)
    ∧ (fi22CentOrderOK 3 = true)
    ∧ (fi22CentOrderOK 4 = true) :=
  facts2066 htext

end CertificateChecks.KernelSpor.Fi22C2066

end
