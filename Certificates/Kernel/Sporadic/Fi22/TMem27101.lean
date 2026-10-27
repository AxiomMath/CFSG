module

public import Certificates.Kernel.Sporadic.Fi22.WordKit
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.TMemFi22Check
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.TMemFi22Check
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import Certificates.Kernel.Sporadic.Fi22.C2068
public import Certificates.Kernel.Sporadic.Fi22.C3151

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.FcParT
  CFSG.EvenSporadicStandard.Induction.TMemFi22Cert.fcParHex
#kmisc_hexflat CertificateChecks.KernelSpor.FcParT
  CFSG.EvenSporadicStandard.Induction.TMemFi22Cert.fcParHex 3 3510 12 1
#ks_chars CertificateChecks.KernelSpor.FcLabT
  CFSG.EvenSporadicStandard.Induction.TMemFi22Cert.fcLabHex
#kmisc_hexflat CertificateChecks.KernelSpor.FcLabT
  CFSG.EvenSporadicStandard.Induction.TMemFi22Cert.fcLabHex 3 3510 12 1
#ks_chars CertificateChecks.KernelSpor.FcDepT
  CFSG.EvenSporadicStandard.Induction.TMemFi22Cert.fcDepHex
#kmisc_hexflat CertificateChecks.KernelSpor.FcDepT
  CFSG.EvenSporadicStandard.Induction.TMemFi22Cert.fcDepHex 3 3510 12 1

namespace CertificateChecks.KernelSpor.TMem27101

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin
open CFSG.Monster.B.Fischer CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Sporadic.FischerOddCore CFSG.EvenSporadicStandard.Induction.TMemFi22Cert
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Fi22W

@[expose] noncomputable def PAR : Nat := FcParT.F 0
@[expose] noncomputable def LAB : Nat := FcLabT.F 0
@[expose] noncomputable def DEP : Nat := FcDepT.F 0
@[expose] noncomputable def T : Nat := Fi22ExtT.L 23

@[expose] noncomputable def hiK (t : Nat) : Bool := Nat.beq (Nat.shiftRight t (3510 * 12)) 0

@[expose] noncomputable def treeK (c1 c2 : Nat) : Bool :=
  allN 3510 fun p =>
    (pg 12 (mask 12) PAR p == p && pg 12 (mask 12) DEP p == 0 &&
        (p == fcR1 || p == fcR2 || p == fcR3)) ||
      (decide (pg 12 (mask 12) PAR p < 3510) &&
        pg 12 (mask 12) DEP p == pg 12 (mask 12) DEP (pg 12 (mask 12) PAR p) + 1 &&
        ((pg 12 (mask 12) LAB p == 1 && pg 12 (mask 12) c1 (pg 12 (mask 12) PAR p) == p) ||
          (pg 12 (mask 12) LAB p == 2 && pg 12 (mask 12) c2 (pg 12 (mask 12) PAR p) == p)))

@[expose] noncomputable def fixK (ts cand : List Nat) : Bool :=
  allN 3510 fun q => !(ts.all fun t => pg 12 (mask 12) t q == q) || cand.contains q

@[expose] noncomputable def consK (ts1 ts2 ts3 : List Nat) : Bool :=
  ts1.all hiK && ts2.all hiK && ts3.all hiK &&
  ts1.all (fun t => pg 12 (mask 12) t fcR1 == fcR1) && fixK ts1 [fcR1] &&
  ts2.all (fun t => pg 12 (mask 12) t fcR2 == fcR2) && fixK ts2 [fcR1, fcR2] &&
  ts3.all (fun t => pg 12 (mask 12) t fcR3 == fcR3) && fixK ts3 [fcR1, fcR3, fcT2R3]

@[expose] noncomputable def sel (a b j : Nat) : Nat := cond (Nat.beq j 0) a b

@[expose] noncomputable def WC (c1 c2 c1i c2i : Nat) (w : List Int) : Nat :=
  wordK 3510 12 (mask 12) (pidn 3510 12) (sel c1 c2) (sel c1i c2i) w

@[expose] noncomputable def forceL (l : List Nat) : (List Nat → Bool) → Bool :=
  List.rec (motive := fun _ => (List Nat → Bool) → Bool) (fun k => k [])
    (fun x _ ih k => strictB x fun x' => ih fun ys => k (x' :: ys)) l

@[expose] noncomputable def chkK (c1 c2 c1i c2i : Nat) : Bool :=
  bAnd(Fi22X.cn c1, bAnd(Fi22X.cn c2, bAnd(Fi22X.cn T,
  bAnd(allN 2 (fun j => permOK 3510 12 (mask 12) (3510 * 12) (sel c1 c2 j) (sel c1i c2i j)),
  bAnd(Nat.beq (Fi22X.c c1 T) (Fi22X.c T c1), bAnd(Nat.beq (Fi22X.c c2 T) (Fi22X.c T c2),
  bAnd(treeK c1 c2,
  forceL (fcCons1.map (WC c1 c2 c1i c2i)) fun ts1 =>
    forceL (fcCons2.map (WC c1 c2 c1i c2i)) fun ts2 =>
      forceL (fcCons3.map (WC c1 c2 c1i c2i)) fun ts3 => consK ts1 ts2 ts3)))))))

@[expose] noncomputable def allK : Bool :=
  strictB (W fcWord1) fun c1 => strictB (W fcWord2) fun c2 =>
    strictB (Fi22X.inv c1) fun c1i => strictB (Fi22X.inv c2) fun c2i => chkK c1 c2 c1i c2i

theorem allOK : allK = true := by quickRfl

theorem lettersOK' : bAnd(lettersK 2 fcWord1, bAnd(lettersK 2 fcWord2,
    (fcCons1 ++ fcCons2 ++ fcCons3).all (lettersK 2))) = true := by quickRfl

theorem tabsHi : bAnd(hiK PAR, bAnd(hiK LAB, hiK DEP)) = true := by quickRfl

private theorem strictB_eq' (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem forceL_eq : ∀ (l : List Nat) (k : List Nat → Bool), forceL l k = k l
  | [], _ => rfl
  | x :: xs, k => by
    change strictB x (fun x' => forceL xs fun ys => k (x' :: ys)) = k (x :: xs)
    rw [strictB_eq', forceL_eq xs]

@[expose] noncomputable def C1 : Nat := W fcWord1
@[expose] noncomputable def C2 : Nat := W fcWord2
@[expose] noncomputable def WCC : List Int → Nat := WC C1 C2 (Fi22X.inv C1) (Fi22X.inv C2)

theorem sel0 (a b : Nat) : sel a b 0 = a := rfl

theorem sel1 (a b : Nat) : sel a b 1 = b := rfl

theorem chk_spec {c1 c2 c1i c2i : Nat} (h : chkK c1 c2 c1i c2i = true) :
    Fi22X.cn c1 = true ∧ Fi22X.cn c2 = true ∧ Fi22X.cn T = true ∧
    allN 2 (fun j => permOK 3510 12 (mask 12) (3510 * 12) (sel c1 c2 j) (sel c1i c2i j)) = true ∧
    Nat.beq (Fi22X.c c1 T) (Fi22X.c T c1) = true ∧ Nat.beq (Fi22X.c c2 T) (Fi22X.c T c2) = true ∧
    treeK c1 c2 = true ∧
    consK (fcCons1.map (WC c1 c2 c1i c2i)) (fcCons2.map (WC c1 c2 c1i c2i))
      (fcCons3.map (WC c1 c2 c1i c2i)) = true := by
  unfold chkK at h
  simp only [bAnd_iff] at h
  rw [forceL_eq, forceL_eq, forceL_eq] at h
  exact h

theorem allK_eq : allK = chkK C1 C2 (Fi22X.inv C1) (Fi22X.inv C2) := by
  unfold allK C1 C2
  rw [strictB_eq', strictB_eq', strictB_eq', strictB_eq']

theorem facts : Fi22X.cn C1 = true ∧ Fi22X.cn C2 = true ∧ Fi22X.cn T = true ∧
    allN 2 (fun j => permOK 3510 12 (mask 12) (3510 * 12) (sel C1 C2 j)
      (sel (Fi22X.inv C1) (Fi22X.inv C2) j)) = true ∧
    Nat.beq (Fi22X.c C1 T) (Fi22X.c T C1) = true ∧ Nat.beq (Fi22X.c C2 T) (Fi22X.c T C2) = true ∧
    treeK C1 C2 = true ∧
    consK (fcCons1.map WCC) (fcCons2.map WCC) (fcCons3.map WCC) = true :=
  chk_spec (by rw [← allK_eq]; exact allOK)

theorem perm1 : permOK 3510 12 (mask 12) (3510 * 12) C1 (Fi22X.inv C1) = true := by
  have h := allN_spec facts.2.2.2.1 0 (by norm_num)
  simp only [sel0] at h
  exact h

theorem perm2 : permOK 3510 12 (mask 12) (3510 * 12) C2 (Fi22X.inv C2) = true := by
  have h := allN_spec facts.2.2.2.1 1 (by norm_num)
  simp only [sel1] at h
  exact h

theorem letters : lettersK 2 fcWord1 = true ∧ lettersK 2 fcWord2 = true ∧
    (fcCons1 ++ fcCons2 ++ fcCons3).all (lettersK 2) = true := by
  have h := lettersOK'
  simp only [bAnd_iff] at h
  exact h

theorem tabs_hi : hiK PAR = true ∧ hiK LAB = true ∧ hiK DEP = true := by
  have h := tabsHi
  simp only [bAnd_iff] at h
  exact h

theorem par_get (i : Nat) : fcPar[i]! = pg 12 (mask 12) PAR i := by
  have h := CFSG.KC.Misc.HexFlat.hexTable3_sound FcParT.all 0 (by norm_num)
  rw [Nat.mul_zero, ← FcParT.eq] at h
  have e : fcPar = unpack 3510 12 PAR := h
  have hh : Nat.shiftRight PAR (3510 * 12) = 0 := Nat.eq_of_beq_eq_true tabs_hi.1
  rw [e, get_eq hh]

theorem lab_get (i : Nat) : fcLab[i]! = pg 12 (mask 12) LAB i := by
  have h := CFSG.KC.Misc.HexFlat.hexTable3_sound FcLabT.all 0 (by norm_num)
  rw [Nat.mul_zero, ← FcLabT.eq] at h
  have e : fcLab = unpack 3510 12 LAB := h
  have hh : Nat.shiftRight LAB (3510 * 12) = 0 := Nat.eq_of_beq_eq_true tabs_hi.2.1
  rw [e, get_eq hh]

theorem dep_get (i : Nat) : fcDep[i]! = pg 12 (mask 12) DEP i := by
  have h := CFSG.KC.Misc.HexFlat.hexTable3_sound FcDepT.all 0 (by norm_num)
  rw [Nat.mul_zero, ← FcDepT.eq] at h
  have e : fcDep = unpack 3510 12 DEP := h
  have hh : Nat.shiftRight DEP (3510 * 12) = 0 := Nat.eq_of_beq_eq_true tabs_hi.2.2
  rw [e, get_eq hh]

theorem t2_eq : fcT2 = unpack 3510 12 T := Fi22E2067.ext_eq (by norm_num)

theorem gen2_bind : fcGen2.size = 2 ∧ ∀ j < 2, fcGen2[j]! = unpack 3510 12 (G j) := by
  refine ⟨rfl, fun j hj => ?_⟩
  interval_cases j
  · have e : fcGen2[0]! = fi22ChainGen 0 := by simp [fcGen2]
    rw [e]
    exact gen_eq (by norm_num)
  · have e : fcGen2[1]! = fi22ChainGen 1 := by simp [fcGen2]
    rw [e]
    exact gen_eq (by norm_num)

theorem gen2i_eq : fcGen2i = rawInvs 3510 fcGen2 := by
  simp [rawInvs, fcGen2, fcGen2i]

theorem c1_eq : fcC1 = unpack 3510 12 C1 := by
  unfold fcC1
  rw [gen2i_eq]
  exact word_eq gen2_bind letters.1

theorem c2_eq : fcC2 = unpack 3510 12 C2 := by
  unfold fcC2
  rw [gen2i_eq]
  exact word_eq gen2_bind letters.2.1

theorem basic : fcBasicCheck = true := by
  obtain ⟨cC1, cC2, cT, -, hc1, hc2, -, -⟩ := facts
  have hp1 := perm1
  have hp2 := perm2
  have g0 := Fi22E2067.isInv_of (gen_eq (k := 0) (by norm_num)) (allN_spec permG 0 (by norm_num))
  have g1 := Fi22E2067.isInv_of (gen_eq (k := 1) (by norm_num)) (allN_spec permG 1 (by norm_num))
  have gT := Fi22E2067.isInv_of t2_eq (Fi22E2067.perm3510 (L := 23) (by norm_num))
  have gC1 := Fi22E2067.isInv_of c1_eq hp1
  have gC2 := Fi22E2067.isInv_of c2_eq hp2
  have m1 : eqA 3510 (compA 3510 fcC1 fcT2) (compA 3510 fcT2 fcC1) = true := by
    rw [c1_eq, t2_eq, Fi22X.comp_eq cC1 cT, Fi22X.comp_eq cT cC1]
    exact Fi22X.eqA_of (Fi22X.cn_c cC1 cT) (Fi22X.cn_c cT cC1) hc1
  have m2 : eqA 3510 (compA 3510 fcC2 fcT2) (compA 3510 fcT2 fcC2) = true := by
    rw [c2_eq, t2_eq, Fi22X.comp_eq cC2 cT, Fi22X.comp_eq cT cC2]
    exact Fi22X.eqA_of (Fi22X.cn_c cC2 cT) (Fi22X.cn_c cT cC2) hc2
  have hT : ∀ i, fcT2[i]! = pg 12 (mask 12) T i := by
    intro i
    rw [t2_eq, get_eq_of_cn cT]
  unfold fcBasicCheck
  simp only [g0, g1, gT, gC1, gC2, m1, m2, hT, Bool.true_and]
  decide +kernel

theorem tree : fcTreeCheck = true := by
  obtain ⟨cC1, cC2, -, -, -, -, ht, -⟩ := facts
  unfold fcTreeCheck
  rw [CFSG.Monster.B.Co2.allLt_iff]
  intro p hp
  have h := allN_spec ht p hp
  simp only [par_get, lab_get, dep_get, c1_eq, c2_eq, get_eq_of_cn cC1, get_eq_of_cn cC2]
  exact h

theorem all_get {ts : List Nat} (hhi : ts.all hiK = true) (i : Nat) :
    (ts.map (unpack 3510 12)).all (fun t => t[i]! == i) =
      ts.all (fun t => pg 12 (mask 12) t i == i) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    rw [List.all_cons, Bool.and_eq_true] at hhi
    rw [List.map_cons, List.all_cons, List.all_cons, get_eq (Nat.eq_of_beq_eq_true hhi.1), ih hhi.2]

theorem fix_of {ts cand : List Nat} (hhi : ts.all hiK = true) (h : fixK ts cand = true) :
    fcFixCover (ts.map (unpack 3510 12)) cand = true := by
  unfold fcFixCover
  rw [CFSG.Monster.B.Co2.allLt_iff]
  intro q hq
  rw [all_get hhi q]
  exact allN_spec h q hq

theorem genC_bind : fcGenC.size = 2 ∧ ∀ j < 2, fcGenC[j]! = unpack 3510 12 (sel C1 C2 j) := by
  refine ⟨rfl, fun j hj => ?_⟩
  interval_cases j
  · have e : fcGenC[0]! = fcC1 := by simp [fcGenC]
    rw [e, sel0]
    exact c1_eq
  · have e : fcGenC[1]! = fcC2 := by simp [fcGenC]
    rw [e, sel1]
    exact c2_eq

theorem genCi_eq : fcGenCi = rawInvs 3510 fcGenC := by
  simp [rawInvs, fcGenC, fcGenCi]

theorem tabs_eq {ws : List (List Int)} (hl : ws.all (lettersK 2) = true) :
    fcTabs ws = (ws.map WCC).map (unpack 3510 12) := by
  obtain ⟨-, -, -, hp, -⟩ := facts
  unfold fcTabs
  rw [genCi_eq, List.map_map]
  refine List.map_congr_left fun w hw => ?_
  exact Fi22W.wordS_eq genC_bind hp (List.all_eq_true.1 hl w hw)

theorem cons : fcConsCheck = true := by
  obtain ⟨-, -, -, -, -, -, -, hc⟩ := facts
  have hl := letters.2.2
  simp only [List.all_append, Bool.and_eq_true] at hl
  obtain ⟨⟨l1, l2⟩, l3⟩ := hl
  unfold consK at hc
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, a1⟩, f1⟩, a2⟩, f2⟩, a3⟩, f3⟩ := hc
  unfold fcConsCheck
  rw [tabs_eq l1, tabs_eq l2, tabs_eq l3, all_get h1, all_get h2, all_get h3, a1, a2, a3,
    fix_of h1 f1, fix_of h2 f2, fix_of h3 f3]
  rfl

theorem check : tmFi22Check = true := by
  unfold tmFi22Check
  rw [basic, tree, cons]
  rfl

end CertificateChecks.KernelSpor.TMem27101

end
