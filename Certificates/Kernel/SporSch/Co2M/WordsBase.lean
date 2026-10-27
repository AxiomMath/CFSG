
module

public import Certificates.Kernel.SporSch.Co2M.Class
public import Certificates.Kernel.SporSch.Co2M.ChainS
public import Certificates.Kernel.SporSch.Co2M.OrbC
public import Certificates.Kernel.SporSch.Co2M.OrbD
public import Certificates.Kernel.SporSch.Co2M.OrbJ
public import CFSG.Sporadic.Co2Schreier.ChainCheckInputs
public meta import CFSG.Sporadic.Co2Schreier.ChainCheckInputs
meta import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Kernel.SporSch.HN.GenNTree
import CFSG.Certificates.Kernel.Common.Harness
import Certificates.Kernel.Misc.Perm.HexCmd
import Certificates.Kernel.SporSch.HN.GenNTree

@[expose] public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Co2M

open CFSG.Sporadic.Co2Schreier

meta def ztArrs : Array (Array Nat) := #[zArr, tArr]

meta def ztMoved : List Nat :=
  [((List.range 2300).find? fun i => zArr[i]! != i).getD 0,
    ((List.range 2300).find? fun i => tArr[i]! != i).getD 0]

end CertificateChecks.KernelSporSch.Co2M

#kmisc_packarrs CertificateChecks.KernelSporSch.Co2M.WQ CFSG.Sporadic.Co2Schreier.qArrs 12
#kmisc_packarrs CertificateChecks.KernelSporSch.Co2M.WR CFSG.Sporadic.Co2Schreier.rArrs 12
#kmisc_packarrs CertificateChecks.KernelSporSch.Co2M.WE CertificateChecks.KernelSporSch.Co2M.ztArrs 12
#kss_ntree CertificateChecks.KernelSporSch.Co2M.ZTW CertificateChecks.KernelSporSch.Co2M.ztMoved

namespace CertificateChecks.KernelSporSch.Co2M

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Co2M CFSG.KS.MatRep CFSG.RankThree.Native.F2
open CFSG.Sporadic.Co2Schreier CFSG.Sporadic.Co2Cert CFSG.Monster.B.Co2.Native
open CFSG.Certificates.Native

@[expose] noncomputable def ztP (k : ℕ) : ℕ × ℕ := if Nat.beq k 0 then zP else tP

theorem bind_q : allN 8 (fun k => bindK (PV 0) (WQ k) (qT.getD k (0, 0)).1
    (qT.getD k (0, 0)).2) = true := by quickRfl

theorem bind_r : allN 10 (fun k => bindK (PV 0) (WR k) (rT.getD k (0, 0)).1
    (rT.getD k (0, 0)).2) = true := by quickRfl

theorem bind_e : allN 2 (fun k => bindK (PV 0) (WE k) (ztP k).1 (ztP k).2) = true := by quickRfl

theorem orig_c : allN 2 (fun k => bindK (PV 0) (Co2LC.S k) (cT.getD k (0, 0)).1
    (cT.getD k (0, 0)).2) = true := by quickRfl

theorem orig_d : allN 2 (fun k => bindK (PV 0) (Co2LD.S k) (dT.getD k (0, 0)).1
    (dT.getD k (0, 0)).2) = true := by quickRfl

theorem orig_s : allN 15 (fun k => bindK (PV 0) (Co2LS.S k) (sT.getD k (0, 0)).1
    (sT.getD k (0, 0)).2) = true := by quickRfl

theorem orig_j : allN 4 (fun k => bindK (PV 0) (Co2LJ.S k) ((cT ++ dT).getD k (0, 0)).1
    ((cT ++ dT).getD k (0, 0)).2) = true := by quickRfl

@[expose] noncomputable def siftS (G : ℕ) : Bool :=
  siftK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) Co2LS.LR Co2LS.TRI Co2LS.BP 3 0 G

theorem sift_q : allN 8 (fun k => siftS (WQ k)) = true := by quickRfl

theorem sift_r : allN 10 (fun k => siftS (WR k)) = true := by quickRfl

theorem sift_e : allN 2 (fun k => siftS (WE k)) = true := by quickRfl

theorem mat_ok : (Nat.beq (cmpP zP zP).1 I22 && Nat.beq (cmpP tP tP).1 I22 &&
    Nat.blt (ZTW 0) 2300 && Nat.blt (ZTW 1) 2300 &&
    !Nat.beq (vmK (VG (PV 0) (ZTW 0)) zP.1) (VG (PV 0) (ZTW 0)) &&
    !Nat.beq (vmK (VG (PV 0) (ZTW 1)) tP.1) (VG (PV 0) (ZTW 1)) &&
    allN 2 (fun k => Nat.beq (cmpP (cT.getD k (0, 0)) zP).1 (cmpP zP (cT.getD k (0, 0))).1) &&
    allN 2 (fun k => Nat.beq (cmpP (dT.getD k (0, 0)) tP).1 (cmpP tP (dT.getD k (0, 0))).1)) =
    true := by quickRfl

theorem lens2 : localRec.qWords.length = 8 ∧ localRec.sQuotientWords.length = 7 := by
  decide +kernel

theorem cInitT_len : cInitT.length = 2 := by rw [cInitT, List.length_map, lens.1]

theorem dT_len : dT.length = 2 := by rw [dT, List.length_map, lens.2.1]

theorem rT_len : rT.length = 10 := by rw [rT, List.length_map, lens.2.2.2.1]

theorem cT_len : cT.length = 2 := by rw [cT, List.length_map, cInitT_len]

theorem qT_len : qT.length = 8 := by rw [qT, List.length_map, lens2.1]

theorem sT_len : sT.length = 15 := by
  rw [sT, List.length_append, qT_len, List.length_map, lens2.2]

theorem rep_unpack {P M M' : ℕ} (h : bindK (PV 0) P M M' = true) :
    MatRep.Rep 22 co2PackedVecs (unpack 2300 12 P) M M' :=
  bindK_sound good V_size (fun _ hi => V_get hi) rfl h

theorem eq_of_rep {a b : Array ℕ} {M M' M'' : ℕ} (ha : MatRep.Rep 22 co2PackedVecs a M M')
    (hb : MatRep.Rep 22 co2PackedVecs b M M'') : a = b := by
  rw [ha.1, hb.1]

theorem unpack_eq {P : ℕ} {a : Array ℕ} {p : ℕ × ℕ} (ha : MatRep.Rep 22 co2PackedVecs a p.1 p.2)
    (h : bindK (PV 0) P p.1 p.2 = true) : unpack 2300 12 P = a :=
  eq_of_rep (rep_unpack h) ha

theorem range_of_bindK {P M M' : ℕ} (h : bindK (PV 0) P M M' = true) :
    allN 2300 (fun i => Nat.blt (pg 12 (mask 12) P i) 2300) = true := by
  unfold bindK at h
  simp only [Bool.and_eq_true] at h
  refine allN_of_forall fun i hi => ?_
  have := allN_spec h.1.1 i hi
  rw [Bool.and_eq_true] at this
  rw [mask12]
  exact this.1

theorem allInv_of_repT {A : Array (Array ℕ)} {T : List (ℕ × ℕ)}
    (hT : RepT 22 co2PackedVecs A T) : allInv A = true := by
  rw [allInv, CFSG.Monster.B.Co2.allLt_iff]
  intro j hj
  exact isInvA_rep (repT_get hT (hT.1 ▸ hj))

theorem sift_of {P : ℕ} {a : Array ℕ} {p : ℕ × ℕ} (ha : MatRep.Rep 22 co2PackedVecs a p.1 p.2)
    (hb : bindK (PV 0) P p.1 p.2 = true) (hs : siftS P = true) :
    siftA 2300 levelsS localRec.chains.S.baseArr 0 a = true :=
  siftK_sound Co2LS.binds Co2LS.perm Co2LS.hl (unpack_eq ha hb).symm (range_of_bindK hb) hs

theorem orig_eqA {c : CFSG.Monster.B.Mathieu.ChainRecord} {PS : ℕ → ℕ} {kS nb BP kO k : ℕ}
    {a : Array ℕ} {p : ℕ × ℕ} (hg : c.generators = c.strongGenerators.take kO)
    (hb : Binds 2300 12 PS kS nb BP c.strongArrs c.baseArr) (hk : k < kO) (hkS : kO ≤ kS)
    (ha : MatRep.Rep 22 co2PackedVecs a p.1 p.2) (h : bindK (PV 0) (PS k) p.1 p.2 = true) :
    eqA 2300 c.origArrs[k]! a = true := by
  obtain ⟨-, -, -, hs, hS, -⟩ := hb
  have e : c.origArrs[k]! = c.strongArrs[k]! := by
    rw [origArrs_eq hg, getElem!_pos _ k (by simp [hs]; omega), Array.getElem_extract,
      getElem!_pos c.strongArrs k (by omega)]
    simp
  rw [e, hS k (by omega), unpack_eq ha h]
  exact eqA_self _ _

theorem eqA_of_mat {a b : Array ℕ} {p q : ℕ × ℕ} (ha : MatRep.Rep 22 co2PackedVecs a p.1 p.2)
    (hb : MatRep.Rep 22 co2PackedVecs b q.1 q.2) (h : p.1 = q.1) : eqA 2300 a b = true := by
  rw [h] at ha
  rw [eq_of_rep ha hb]
  exact eqA_self _ _

theorem ne_of_mat {a : Array ℕ} {p : ℕ × ℕ} (ha : MatRep.Rep 22 co2PackedVecs a p.1 p.2) {i : ℕ}
    (hi : i < 2300) (h : Nat.beq (vmK (VG (PV 0) i) p.1) (VG (PV 0) i) = false) :
    eqA 2300 a (idA 2300) = false := by
  cases hc : eqA 2300 a (idA 2300)
  · rfl
  · exfalso
    have hx := CFSG.Monster.B.Co2.allLt_iff.1 hc i hi
    rw [CFSG.Monster.B.Co2.idA_get hi, beq_iff_eq] at hx
    have hg := (get_rep ha (i := i) (by rw [V_size]; exact hi)).2
    rw [hx, V_get hi, ← vmK_eq] at hg
    rw [← hg, Nat.beq_refl] at h
    exact Bool.false_ne_true h.symm

theorem rep_ztP0 : MatRep.Rep 22 co2PackedVecs zArr (ztP 0).1 (ztP 0).2 := zRep

theorem rep_ztP1 : MatRep.Rep 22 co2PackedVecs tArr (ztP 1).1 (ztP 1).2 := tRep

end CertificateChecks.KernelSporSch.Co2M

end
