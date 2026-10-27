module

public import Certificates.Kernel.SporSch.Co2M.Local
public import CFSG.Certificates.Kernel.SporSch.SpanKSound
public import CFSG.Monster.B.Co2.PermArr
public meta import CFSG.Sporadic.Co2Schreier.QCheckInputs
meta import Certificates.Kernel.SporSch.HN.GenNTree
import Certificates.Kernel.SporSch.Co2M.Six
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import all Init.Data.Array.Basic

public section

set_option maxRecDepth 400000
set_option exponentiation.threshold 600

namespace CertificateChecks.KernelSporSch.Co2M

open CFSG.Sporadic.Co2Schreier CFSG.Sporadic.SmallF2.Native

meta def spanTabs : List Nat := [0, 1].map fun i =>
  (List.range 256).foldl (fun acc a => acc ||| (vecMulN 8 (qActCols witRec i) a <<< (8 * a))) 0

end CertificateChecks.KernelSporSch.Co2M

#kss_ntree CertificateChecks.KernelSporSch.Co2M.QTab CertificateChecks.KernelSporSch.Co2M.spanTabs

namespace CertificateChecks.KernelSporSch.Co2M

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Co2M CFSG.KS.MatRep CFSG.KS.SpanK
open CFSG.RankThree.Native.F2
open CFSG.Sporadic.Co2Schreier CFSG.Sporadic.Co2Cert CFSG.Monster.B.Co2.Native
open CFSG.Certificates.Native CFSG.Sporadic.SmallF2.Native

@[expose] def RL : List (List ℕ) :=
  [[197, 203, 119, 5, 22, 154, 134, 105], [162, 62, 198, 44, 52, 155, 88, 188]]

theorem rows_eq : witRec.wLocal.qQuotientActionRows = RL := by decide +kernel

@[expose] def colsL (i : ℕ) : Array ℕ := transposeRows 8 (RL.getD i []).toArray

@[expose] def colL (i l : ℕ) : ℕ := (colsL i)[l]?.getD 0

@[expose] def thetaL (a : ℕ) : ℕ := a ^^^ vecMulN 8 (colsL 0) a ^^^ vecMulN 8 (colsL 1) a

@[expose] noncomputable def prodP (l : List ℕ) : ℕ × ℕ :=
  l.foldl (fun acc i => cmpP acc (qT.getD i (0, 0))) (I22, I22)

@[expose] noncomputable def oneOrZK (X : ℕ) : Bool := Nat.beq X I22 || Nat.beq X zP.1

@[expose] noncomputable def prodOrZK (X w : ℕ) : Bool :=
  Nat.beq X (prodP (bits8 w)).1 || Nat.beq X (cmpP (prodP (bits8 w)) zP).1

@[expose] noncomputable def qGroupK : Bool :=
  allLt 8 (fun k => oneOrZK (cmpP (qT.getD k (0, 0)) (qT.getD k (0, 0))).1) &&
  allLt 8 (fun k => allLt 8 fun l => oneOrZK (cmpP (cmpP (cmpP (qT.getD k (0, 0))
    (qT.getD l (0, 0))) (invP (qT.getD k (0, 0)))) (invP (qT.getD l (0, 0)))).1) &&
  allLt 2 (fun i => allLt 8 fun l => prodOrZK (cmpP (cmpP (cT.getD i (0, 0))
    (qT.getD l (0, 0))) (invP (cT.getD i (0, 0)))).1 (colL i l))

theorem qGroup_ok : qGroupK = true := by decide +kernel

theorem colTheta_ok : (allLt 2 (fun i => allLt 8 fun l => decide (colL i l < 256)) &&
    colL 0 0 == 143 &&
    allLt 256 (fun a => decide (thetaL a < 256) && (thetaL a != 0 || a == 0 || a == 218)) &&
    thetaL 218 == 0) = true := by
  decide +kernel

theorem basis_ok : witRec.wLocal.qQuotientBasisIndices = [1, 2, 3, 4, 5, 6, 7, 8] := by
  decide +kernel

theorem tab_ok : allN 256 (fun a => Nat.beq (tabK (QTab 0) a) (vecMulN 8 (colsL 0) a) &&
    Nat.beq (tabK (QTab 1) a) (vecMulN 8 (colsL 1) a)) = true := by
  decide +kernel

@[expose] noncomputable def spanAt (v : ℕ) : Bool :=
  bif Nat.blt v 255 then Nat.beq (iterK (tabK (QTab 0)) (tabK (QTab 1)) 8 (insK 1 (Nat.succ v)))
    (Nat.sub (Nat.shiftLeft 1 256) 1) else true

theorem span0 : allN 16 (fun t => spanAt (Nat.add 0 t)) = true := by quickRfl
theorem span1 : allN 16 (fun t => spanAt (Nat.add 16 t)) = true := by quickRfl
theorem span2 : allN 16 (fun t => spanAt (Nat.add 32 t)) = true := by quickRfl
theorem span3 : allN 16 (fun t => spanAt (Nat.add 48 t)) = true := by quickRfl
theorem span4 : allN 16 (fun t => spanAt (Nat.add 64 t)) = true := by quickRfl
theorem span5 : allN 16 (fun t => spanAt (Nat.add 80 t)) = true := by quickRfl
theorem span6 : allN 16 (fun t => spanAt (Nat.add 96 t)) = true := by quickRfl
theorem span7 : allN 16 (fun t => spanAt (Nat.add 112 t)) = true := by quickRfl
theorem span8 : allN 16 (fun t => spanAt (Nat.add 128 t)) = true := by quickRfl
theorem span9 : allN 16 (fun t => spanAt (Nat.add 144 t)) = true := by quickRfl
theorem span10 : allN 16 (fun t => spanAt (Nat.add 160 t)) = true := by quickRfl
theorem span11 : allN 16 (fun t => spanAt (Nat.add 176 t)) = true := by quickRfl
theorem span12 : allN 16 (fun t => spanAt (Nat.add 192 t)) = true := by quickRfl
theorem span13 : allN 16 (fun t => spanAt (Nat.add 208 t)) = true := by quickRfl
theorem span14 : allN 16 (fun t => spanAt (Nat.add 224 t)) = true := by quickRfl
theorem span15 : allN 16 (fun t => spanAt (Nat.add 240 t)) = true := by quickRfl

theorem span_k (v : ℕ) (hv : v < 255) : Nat.beq (iterK (tabK (QTab 0)) (tabK (QTab 1)) 8
    (insK 1 (Nat.succ v))) (Nat.sub (Nat.shiftLeft 1 256) 1) = true := by
  have hc : ∀ s < 16, ∀ t < 16, spanAt (Nat.add (16 * s) t) = true := by
    intro s hs t ht
    interval_cases s
    exacts [allN_spec span0 t ht, allN_spec span1 t ht, allN_spec span2 t ht,
      allN_spec span3 t ht, allN_spec span4 t ht, allN_spec span5 t ht, allN_spec span6 t ht,
      allN_spec span7 t ht, allN_spec span8 t ht, allN_spec span9 t ht, allN_spec span10 t ht,
      allN_spec span11 t ht, allN_spec span12 t ht, allN_spec span13 t ht,
      allN_spec span14 t ht, allN_spec span15 t ht]
  have h := hc (v / 16) (by omega) (v % 16) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (16 * (v / 16)) (v % 16) = v := Nat.div_add_mod v 16
  rw [e] at h
  have hb : Nat.blt v 255 = true := by rw [Nat.blt_eq]; exact hv
  unfold spanAt at h
  rw [hb, Bool.cond_true] at h
  exact h

theorem eqA_mat {a b : Array ℕ} {A B : ℕ} (ha : a = permOfMat 22 co2PackedVecs A)
    (hb : b = permOfMat 22 co2PackedVecs B) (h : A = B) : eqA 2300 a b = true := by
  rewrite [ha, hb, h, eqA, CFSG.Monster.B.Co2.allLt_iff]
  intro i _
  exact beq_self_eq_true _

theorem idA_eq' : idA 2300 = permOfMat 22 co2PackedVecs I22 := by
  rw [I22_eq, permOfMat_idM good.hd good.nodup good.lt, V_size]

theorem oneOrZ_of {t : Array ℕ} {p : ℕ × ℕ} (ht : MatRep.Rep 22 co2PackedVecs t p.1 p.2)
    (h : oneOrZK p.1 = true) : isOneOrZ t = true := by
  unfold isOneOrZ
  unfold oneOrZK at h
  rcases Bool.or_eq_true_iff.1 h with h1 | h1
  · rewrite [eqA_mat ht.1 idA_eq' (Nat.eq_of_beq_eq_true h1)]
    rfl
  · rewrite [eqA_mat ht.1 zRep.1 (Nat.eq_of_beq_eq_true h1), Bool.or_true]
    rfl

theorem c_len' : cT.length = 2 := by rw [cT, List.length_map, cInitT, List.length_map, lens.1]

theorem rep_prodFold (l : List ℕ) (hl : ∀ i ∈ l, i < 8) :
    ∀ (a : Array ℕ) (p : ℕ × ℕ), MatRep.Rep 22 co2PackedVecs a p.1 p.2 →
      MatRep.Rep 22 co2PackedVecs (l.foldl (fun acc i => compA 2300 acc qArrs[i]!) a)
        (l.foldl (fun acc i => cmpP acc (qT.getD i (0, 0))) p).1
        (l.foldl (fun acc i => cmpP acc (qT.getD i (0, 0))) p).2 := by
  induction l with
  | nil => intro a p h; exact h
  | cons i l ih =>
    intro a p h
    rw [List.foldl_cons, List.foldl_cons]
    exact ih (fun j hj => hl j (List.mem_cons_of_mem _ hj)) _ _
      (rep_cmp h (repT_get qRep (by rw [q_len]; exact hl i List.mem_cons_self)))

theorem rep_qProd (w : ℕ) :
    MatRep.Rep 22 co2PackedVecs (qProdArr w) (prodP (bits8 w)).1 (prodP (bits8 w)).2 := by
  unfold qProdArr prodArr prodP
  have h := rep_idA good
  rw [V_size, ← I22_eq] at h
  exact rep_prodFold _ (fun i hi => by
    unfold bits8 at hi
    exact List.mem_range.1 (List.mem_filter.1 hi).1) _ (I22, I22) h

theorem prodOrZ_of {t : Array ℕ} {p : ℕ × ℕ} (ht : MatRep.Rep 22 co2PackedVecs t p.1 p.2) (w : ℕ)
    (h : prodOrZK p.1 w = true) : isProdOrZ t w = true := by
  unfold isProdOrZ
  unfold prodOrZK at h
  rcases Bool.or_eq_true_iff.1 h with h1 | h1
  · rewrite [eqA_mat ht.1 (rep_qProd w).1 (Nat.eq_of_beq_eq_true h1)]
    rfl
  · rewrite [eqA_mat ht.1 (rep_cmp (rep_qProd w) zRep).1 (Nat.eq_of_beq_eq_true h1), Bool.or_true]
    rfl

theorem spanIter_ok : allLt 255 (fun v => spanIter (colsL 0) (colsL 1) 8 (spanIns 1 (v + 1)) ==
    2 ^ 256 - 1) = true := by
  have ht := tab_ok
  have h0 : ∀ a < 256, tabK (QTab 0) a = vecMulN 8 (colsL 0) a := fun a ha => by
    have := allN_spec ht a ha
    rw [Bool.and_eq_true] at this
    exact Nat.eq_of_beq_eq_true this.1
  have h1 : ∀ a < 256, tabK (QTab 1) a = vecMulN 8 (colsL 1) a := fun a ha => by
    have := allN_spec ht a ha
    rw [Bool.and_eq_true] at this
    exact Nat.eq_of_beq_eq_true this.2
  have hf : Nat.sub (Nat.shiftLeft 1 256) 1 = 2 ^ 256 - 1 := by rfl
  rw [CFSG.Monster.B.Co2.allLt_iff]
  intro v hv
  have hk := Nat.eq_of_beq_eq_true (span_k v hv)
  rw [iterK_eq h0 h1, insK_eq, hf] at hk
  rw [hk]
  exact beq_self_eq_true _

theorem qmod_check : qmodCheck witRec = true := by
  have hg := qGroup_ok
  unfold qGroupK at hg
  simp only [Bool.and_eq_true] at hg
  obtain ⟨⟨hsq, hcm⟩, hcj⟩ := hg
  have hr := colTheta_ok
  simp only [Bool.and_eq_true] at hr
  obtain ⟨⟨⟨hcol, h143⟩, hth⟩, h218⟩ := hr
  have hq : ∀ k < 8, MatRep.Rep 22 co2PackedVecs qArrs[k]! (qT.getD k (0, 0)).1
      (qT.getD k (0, 0)).2 := fun k hk => repT_get qRep (by rw [q_len]; exact hk)
  have hc : ∀ i < 2, MatRep.Rep 22 co2PackedVecs cArrs[i]! (cT.getD i (0, 0)).1
      (cT.getD i (0, 0)).2 := fun i hi => repT_get cRep (by rw [c_len']; exact hi)
  have eC : ∀ i, qActCols witRec i = colsL i := fun i => by
    unfold qActCols qActRows colsL
    rw [rows_eq]
  have eq : ∀ i l, qCol witRec i l = colL i l := fun i l => by
    unfold qCol colL
    rw [eC]
  have eθ : thetaN witRec = thetaL := by
    funext a
    unfold thetaN thetaL
    rw [eC, eC]
  unfold qmodCheck
  simp only [Bool.and_eq_true, eq, eθ, eC, basis_ok]
  refine ⟨⟨⟨⟨⟨⟨⟨rfl, ?_⟩, ?_⟩, ?_⟩, h143⟩, spanIter_ok⟩, hth⟩, h218⟩
  · rw [CFSG.Monster.B.Co2.allLt_iff] at hsq ⊢
    intro k hk
    exact oneOrZ_of (rep_cmp (hq k hk) (hq k hk)) (hsq k hk)
  · rw [CFSG.Monster.B.Co2.allLt_iff] at hcm ⊢
    intro k hk
    have hk' := hcm k hk
    rw [CFSG.Monster.B.Co2.allLt_iff] at hk' ⊢
    intro l hl
    exact oneOrZ_of (rep_cmp (rep_cmp (rep_cmp (hq k hk) (hq l hl)) (rep_inv (hq k hk)))
      (rep_inv (hq l hl))) (hk' l hl)
  · rw [CFSG.Monster.B.Co2.allLt_iff] at hcj hcol ⊢
    intro i hi
    have hi' := hcj i hi
    have hc' := hcol i hi
    rw [CFSG.Monster.B.Co2.allLt_iff] at hi' hc' ⊢
    intro l hl
    rw [Bool.and_eq_true]
    exact ⟨hc' l hl, prodOrZ_of (rep_cmp (rep_cmp (hc i hi) (hq l hl)) (rep_inv (hc i hi))) _
      (hi' l hl)⟩

end CertificateChecks.KernelSporSch.Co2M

end
